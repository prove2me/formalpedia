-- Prove2me | Theorems.Thm_MazurReduction_odd_prime_division_nonzero
-- name    : MazurReduction.odd_prime_division_nonzero
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T10:35:35.987127+00:00
-- url     : https://prove2.me/theorems/e2b978a1-6a7a-4521-9332-095a5880effb
-- title:
--   Odd-prime division polynomials do not vanish at nonintegral rational points
-- statement:
--   For an odd prime p>2 and an integral rational Weierstrass equation over its p-adic valuation subring, the p-th odd division polynomial is nonzero at the abscissa of any rational affine solution outside the valuation subring. This supplies the residue-characteristic part of the intended torsion-kernel exclusion; it does not yet assert injectivity of a reduction map.
-- source:
--   New Mazur campaign proof, Vasily Ilin, October 2026; coordinate input: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_WeierstrassCurve_TorsionIntegral.lean ; polynomial leading coefficient: Mathlib AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom
import Theorems.Thm_MazurReduction_abscissa_valuation_ge_two
import Theorems.Thm_MazurReduction_leading_coefficient_root_bound
open WithZero
open MazurReduction

theorem MazurReduction.odd_prime_division_nonzero
    (p : ℕ) [Fact p.Prime] (hp : 2 < p)
    (W : WeierstrassCurve (Rat.padicValuation p).valuationSubring)
    {x y : ℚ}
    (h : (W.map (Rat.padicValuation p).valuationSubring.subtype).toAffine.Equation x y)
    (hx : x ∉ (Rat.padicValuation p).valuationSubring) :
    ((W.map (Rat.padicValuation p).valuationSubring.subtype).preΨ' p).eval x ≠ 0 := by sorry
