-- Prove2me | Theorems.Thm_MazurReduction_abscissa_valuation_ge_two
-- name    : MazurReduction.abscissa_valuation_ge_two
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T10:15:01.71976+00:00
-- url     : https://prove2.me/theorems/bd4bac9e-a435-4ee1-b67f-5a9e322796ee
-- title:
--   Nonintegral rational Weierstrass abscissae have valuation at least two
-- statement:
--   For a prime p, an integral Weierstrass equation over the p-adic valuation subring of the rationals, and any rational affine solution (x,y), if x is outside that valuation subring then its multiplicative valuation is at least exp(2). No ellipticity or torsion hypothesis is assumed.
-- source:
--   New Mazur campaign proof, Vasily Ilin, October 2026; coordinate input: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_WeierstrassCurve_TorsionIntegral.lean ; polynomial leading coefficient: Mathlib AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom
open WithZero

theorem MazurReduction.abscissa_valuation_ge_two
    (p : ℕ) [Fact p.Prime]
    (W : WeierstrassCurve (Rat.padicValuation p).valuationSubring)
    {x y : ℚ} (h : (W.map (Rat.padicValuation p).valuationSubring.subtype).toAffine.Equation x y)
    (hx : x ∉ (Rat.padicValuation p).valuationSubring) :
    exp (2 : ℤ) ≤ Rat.padicValuation p x := by sorry
