# OEIS A192473 — Proof of Colin Barker's recurrence conjecture

This repository contains a Lean 4 / Mathlib proof of the fourth-order recurrence conjectured by Colin Barker for [OEIS A192473](https://oeis.org/A192473).

**Verification:** `A192473_v2.lean` compiled successfully in Google Colab on November 23, 2026, as reported by the contributor. The compiler produced only warnings about unused `simp` arguments. The `#print axioms` reports for all four main theorems contained no `sorryAx`; the reported dependencies were standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Sequence and conjecture

For each nonnegative integer `n`, reduce

\[
P_n(X)=1+X^n+X^{2n+2}
\]

using `X² = X + 1`. Write the unique reduced representative as `u_n + a_n X`. The auxiliary coefficient sequence is `a_n`. **OEIS A192473 has offset 1 and starts at polynomial index 1:** OEIS `A192473(n) = a_n` for `n >= 1`. The auxiliary value `a_0 = 1` is not part of the OEIS sequence. The OEIS initial values are `4, 9, 23, 58, ...`.

Barker's conjecture is

\[
a_{n+4}=4a_{n+3}-3a_{n+2}-2a_{n+1}+a_n \quad(n\geq 0).
\]

## Mathematical proof

In the quadratic algebra `Z[X]/(X²-X-1)`, the element `X` satisfies `X²=X+1`. Therefore the coefficient sequences of `X^n` satisfy the characteristic polynomial

\[
f(T)=T^2-T-1.
\]

Put `Y=X²=X+1`. Then `Y²=3Y-1`, so the coefficient sequences of `X^(2n+2)=Y^(n+1)` satisfy

\[
g(T)=T^2-3T+1.
\]

The constant polynomial `1` contributes zero to the coefficient of `X`. Thus `a_n` is the sum of the `X` coefficients of `X^n` and `X^(2n+2)`. A product of annihilating operators annihilates that sum:

\[
\begin{aligned}
f(T)g(T)
&=(T^2-T-1)(T^2-3T+1)\\
&=T^4-4T^3+3T^2+2T-1.
\end{aligned}
\]

Consequently,

\[
a_{n+4}-4a_{n+3}+3a_{n+2}+2a_{n+1}-a_n=0,
\]

which proves the OEIS conjectured recurrence for every OEIS index `n >= 5`.

## Lean formalization

The file [`A192473_v2.lean`](A192473_v2.lean) contains:

- `Barker473.a192473_recurrence`: the recurrence for the coefficient sequence;
- `Barker473.fibPair_eval`: evaluation of the reduced coordinates of `X^n`;
- `Barker473.pellPair_eval`: evaluation of the reduced coordinates of `X^(2n+2)`;
- `Barker473.a192473_polynomial_bridge`: identification with the defining polynomial `1 + X^n + X^(2n+2)` under `X² = X+1`.

Compile inside a Lean 4 project with Mathlib installed:

```bash
lake env lean A192473_v2.lean
```

The source uses explicit degree-less-than-two coefficient pairs and proves their evaluation property. It does **not** state a separate theorem using Mathlib's `Polynomial.modByMonic` operation. The equivalence with the canonical polynomial remainder follows mathematically from uniqueness of the degree-less-than-two representative modulo the monic quadratic.

## Attribution and status

- **Sequence:** [OEIS A192473](https://oeis.org/A192473).
- **Original recurrence conjecture:** Colin Barker, June 7, 2019 (as recorded in OEIS).
- **Proof and Lean formalization:** Shreyas Samir Kolte, November 23, 2026, with AI assistance.

The method uses established linear-recurrence and quotient-algebra theory. This repository documents an explicit proof of the stated OEIS conjecture; it does not claim that the underlying algebraic technique is new. The available OEIS history showed no earlier recorded proof, but independent worldwide priority has not been conclusively established. OEIS editorial acceptance is separate from Lean verification.
