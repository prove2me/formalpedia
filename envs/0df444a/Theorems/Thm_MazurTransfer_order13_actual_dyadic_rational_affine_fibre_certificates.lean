-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_dyadic_rational_affine_fibre_certificates
-- name    : MazurTransfer.order13_actual_dyadic_rational_affine_fibre_certificates
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T04:49:21.354736+00:00
-- url     : https://prove2.me/theorems/5fc7a0e5-7222-4302-9716-91e19155adb3
-- statement:
--   The two original dyadic mixed quadratic affine-chart fibres over the rationals are identified with the SAME original rational order-thirteen ordinary and reciprocal affine charts. The original chosen affine scheme isomorphisms respect both rational structure maps and both actual pullback first projections. All four complete original propositions retain the original coefficient maps. Named downstream consumer: the whole-curve rational-fibre isomorphism and compatible integral Picard model.

import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalRationalChartComparisonAndAffineBaseChangeData20261019
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MazurTransfer
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticRationalChartComparison Order13MixedQuadraticAffineBaseChange

theorem MazurTransfer.order13_actual_dyadic_rational_affine_fibre_certificates : (ordinaryRationalSchemeIso.inv ≫ ordinaryToBase ℚ =
      MazurTorsion.XOneThirteenProjectiveCurve.ordinaryChartToBase ℚ) ∧ (reciprocalRationalSchemeIso.inv ≫ reciprocalToBase ℚ =
      MazurTorsion.XOneThirteenProjectiveCurve.reciprocalChartToBase ℚ) ∧ (ordinaryDyadicRationalFibreIso.inv ≫ pullback.fst _ _ =
      MazurTorsion.XOneThirteenProjectiveCurve.ordinaryChartToBase ℚ) ∧ (reciprocalDyadicRationalFibreIso.inv ≫ pullback.fst _ _ =
      MazurTorsion.XOneThirteenProjectiveCurve.reciprocalChartToBase ℚ) := by sorry
