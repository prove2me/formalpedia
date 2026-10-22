-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomial_curve_aeval_pole_le_weighted_height
-- name    : OAI.PiExponent.FormalInterpolation.polynomial_curve_aeval_pole_le_weighted_height
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:41:31.541988+00:00
-- url     : https://prove2.me/theorems/a88160a1-f5d4-40af-b023-aba06a1241e2
-- title:
--   Polynomial evaluation poles are bounded by weighted height times coordinate poles
-- statement:
--   Let $\nu$ be a normalized place, let $w_i>0$ be weights, and let $F$ be a polynomial whose support has weighted degree at most $N\ge 0$. Then the pole order of the evaluation $F(x)$ at $\nu$ satisfies
--   $$\max(-\operatorname{ord}_\nu(F(x)),0)\le N\cdot\mathrm{Pole}_\nu(x,w).$$
--   This is the placewise form of the weighted polynomial pole bound (compare OpenAI `PolynomialPoleBound` / `WeightedPolynomialPole`): each monomial of weight $\le N$ has valuation at least $-N\cdot\mathrm{Pole}_\nu$, and the valuation of a sum is at least the minimum of the summands.
-- source:
--   OpenAI math repo lean/OAI/NumberTheory/PiExponent/Polynomials/PolynomialPoleBound.lean and WeightedPolynomialPole.lean (framePolynomial_order_lower); reduction obligation for polynomial_curve_zero_divisor_bound on Prove2Me.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.polynomial_curve_aeval_pole_le_weighted_height
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (N : Real) (hN : 0 ≤ N)
    (F : MvPolynomial (Fin d) Complex)
    (hF : logarithmicDegreeBound w N F) :
    max (-(polynomialCurveOrder nu (MvPolynomial.aeval x F) : Real)) 0 ≤
      N * polynomialCurvePole nu x w := by sorry
