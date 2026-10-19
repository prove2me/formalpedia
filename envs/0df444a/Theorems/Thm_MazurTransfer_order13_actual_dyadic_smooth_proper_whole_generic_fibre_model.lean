-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_dyadic_smooth_proper_whole_generic_fibre_model
-- name    : MazurTransfer.order13_actual_dyadic_smooth_proper_whole_generic_fibre_model
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T05:18:10.683722+00:00
-- url     : https://prove2.me/theorems/bcbec058-9c64-4d78-a6a1-2ef14f3f965b
-- statement:
--   The actual glued mixed quadratic curve over Z localized at two is proper, smooth, flat and locally of finite presentation, has its finite hyperelliptic map, and has its whole rational generic fibre isomorphic to the original rational order-thirteen curve over Spec Q. The chosen whole generic-fibre isomorphism and its whole value are independently retained. Named downstream consumer: the compatible Picard and norm families at two.

import Definitions.Def_MazurTransfer_Order13ActualDyadicOriginalWholeGenericFibreIsomorphismData20261019
import Theorems.Thm_MazurTransfer_order13_actual_dyadic_glued_curve_geometry
import Theorems.Thm_MazurTransfer_order13_actual_mixed_quadratic_curve_proper
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MazurTransfer
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve Order13ActualDyadicMixedQuadraticGenericFibre

theorem MazurTransfer.order13_actual_dyadic_smooth_proper_whole_generic_fibre_model : (IsProper (curveToBase BaseRing) ∧ Smooth (curveToBase BaseRing) ∧
      Flat (curveToBase BaseRing) ∧ LocallyOfFinitePresentation (curveToBase BaseRing)) ∧ (IsFinite (Order13MixedQuadraticProperCurve.hyperellipticMap BaseRing)) ∧ (IsProper (curveToBase BaseRing) ∧ Smooth (curveToBase BaseRing) ∧
      Flat (curveToBase BaseRing) ∧ LocallyOfFinitePresentation (curveToBase BaseRing) ∧
      ∃ e : pullback (Spec.map (CommRingCat.ofHom (algebraMap BaseRing ℚ))) (curveToBase BaseRing) ≅
          MazurTorsion.XOneThirteenProjectiveCurve.curveScheme ℚ,
        e.inv ≫ pullback.fst _ _ = MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) := by sorry
