-- Prove2me | Theorems.Thm_IntegerRootsFN_Main_proposition_3_4_computation
-- name    : IntegerRootsFN.Main.proposition_3_4_computation
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:17:40.451787+00:00
-- url     : https://prove2.me/theorems/47c5c810-0d60-4bef-b37f-6f518d31a934
-- title:
--   Proposition 3.4 — finite-machine construction and output size
-- statement:
--   Let $g\in\mathbb Z[x]$ have exact degree $d\ge1$ and coefficient magnitudes below $2^b$, with $b\ge1$. This is the computational part of Proposition 3.4: one deterministic finite multitape machine performs the shift of Lemma 3.3, reverses the shifted coefficients to form $H(w)=w^dg(q+1/w)$, invokes approximate factorization at the prescribed precision $P$, and computes represented Gaussian rationals $\beta_i=q+1/w_i$.
--
--   The emitted shift satisfies $|q|\le10d^2+1$ and has distance greater than $1$ from every root of $g$. The returned common-dyadic factors $w_i$ satisfy
--   $$
--   \left\|H-H_d\prod_{i=1}^d(X-w_i)\right\|_1\le 2^{-P}\|H\|_1,
--   $$
--   and their denominator exponent is $B=O(P)$. All intermediate records and the final rationals are written by the same run, in time $\widetilde O(d(b+d))$, and the total mathematical size of the $\beta_i$ obeys the same bound. The machine, positive constant, and fixed logarithmic exponents are uniform over all valid inputs.
--
--   This statement deliberately leaves nonvanishing of the $w_i$, root coverage, and aggregate logarithmic root size to the separate analytic inverse-transform obligation. It is the literal implementation and output-size content of Steps 1–3 on pp.9–10, using Lemma 3.3 and Theorem 3.1.
-- source:
--   Yansong Feng, Itamar Nir, STOC 2027 submission #1353 (October 2026), pp. 9–10, proof of Proposition 3.4, Steps 1–3 and final running-time and bit-size paragraph; inputs supplied by Lemma 3.3 p.8 and Theorem 3.1 p.7

import Mathlib
import Definitions.Def_IntegerRootsFN_Main_Binary
import Definitions.Def_IntegerRootsFN_Main_ApproximationConstruction

set_option autoImplicit false

namespace IntegerRootsFN.Main

theorem proposition_3_4_computation :
    ∃ M : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧ ∃ k l : ℕ,
    ∀ (d b : ℕ) (g : Polynomial ℤ), Valid g d b →
    ∃ (samples : Fin (d + 1) → ApproxGKR.GaussDyadic) (q : ℤ × ℤ)
      (B : ℕ) (ws : Fin d → ℤ × ℤ) (β : Fin d → GaussianRational),
      ShiftChoice g d samples q ∧
      ‖gaussianValue q‖ ≤ 10 * (d : ℝ) ^ 2 + 1 ∧
      (∀ α : ℂ, (complexify g).IsRoot α → 1 < ‖α - gaussianValue q‖) ∧
      normOne (reverseShift g d q -
        factorPolynomial ((reverseShift g d q).coeff d)
          (fun i => ApproxGKR.dyadicVal ((ws i).1, (ws i).2, B))) ≤
        (2 : ℝ) ^ (-(approximationPrecision d b : ℤ)) * normOne (reverseShift g d q) ∧
      (∀ i, (β i).value = gaussianValue q +
        1 / ApproxGKR.dyadicVal ((ws i).1, (ws i).2, B)) ∧
      (B : ℝ) ≤ C * approximationPrecision d b ∧
      (∑ i, ((β i).bitSize : ℝ)) ≤ softBound C k l d b ((d : ℝ) * (b + (d : ℝ))) ∧
      Runs M (polynomialWord g d b) (approximationOutputWord samples q B ws β)
        (softBound C k l d b ((d : ℝ) * (b + (d : ℝ)))) := by sorry
