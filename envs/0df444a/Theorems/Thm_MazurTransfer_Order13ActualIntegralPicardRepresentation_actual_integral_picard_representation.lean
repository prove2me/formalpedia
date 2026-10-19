-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualIntegralPicardRepresentation_actual_integral_picard_representation
-- name    : MazurTransfer.Order13ActualIntegralPicardRepresentation.actual_integral_picard_representation
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T07:22:40.790934+00:00
-- url     : https://prove2.me/theorems/cc884152-8c0b-419d-9aed-6f55f1323d3e
-- title:
--   Actual integral Picard representation for the order-thirteen curve
-- statement:
--   Let $R$ be a noetherian commutative integral domain in which $104$ is invertible. Let $C/R$ be the literal order-thirteen curve with its specified positive-infinity section $\varepsilon$. The relative subfunctor of algebraically trivial line bundles, with the specified rigidification along $\varepsilon$, has an actual designated representing scheme $D$. Its structure morphism satisfies $$D\longrightarrow\operatorname{Spec}R\quad\text{is smooth, proper and geometrically connected}. $$ The represented subfunctor is precisely the original algebraic-equivalence-zero cut for $C/R$ and $\varepsilon$. This supplies the integral Picard-family representation used for the actual rational and good-characteristic fibres.
-- source:
--   Original actual_integral_picard_representation contract from MazurTheorem Order13ActualIntegralPicardRepresentation.lean, Apache-2.0, Vas and contributors. Reuses the original official Anthropic FLT representability theorem at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2. The original final representability application is retained, with the actual arbitrary-degree integral FiniteMapData constructors and already Proved public properness, stronger relative-dimension-one, geometric-integrality and 216-triple chart-section inputs. The complete 3585-character original closed kernel type is independently exported and compared with both the checked solution and public formal statement; every hypothesis, actual curve, section, subfunctor and conclusion is retained. No equality with an older chosen finite-map witness or Picard representative is asserted. Native, strict and full frontend checks pass with standard axioms only. Original per-file header and upstream attribution are retained. Named downstream consumers: compatible actual integral Jacobian family and rational/mod-3/mod-5 Picard-fibre identification.

import Mathlib
import Definitions.Def_MazurTransfer_Order13FiniteMapDataFromPublicCharts
import Definitions.Def_MazurTransfer_Order13ActualPicardTripleFamily
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_proper
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_smooth_relative_dimension_one
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_geometrically_integral
import Theorems.Thm_MazurTransfer_Order13ActualIntegralPicardChartSections_actual_hasChartSections
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_algEquivZeroCut_of_finiteMapData_of_isReduced
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer

theorem MazurTransfer.Order13ActualIntegralPicardRepresentation.actual_integral_picard_representation (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] (h104 : IsUnit (104 : R)) :
    ∃ D : RelativePic0Designation R (curveToBase R),
      Nonempty (RepresentsRelSubPic (curveToBase R)
        (Order13IntegralSections.positiveInfinitySection R)
        (algEquivZeroCut (curveToBase R) (Order13IntegralSections.positiveInfinitySection R)) D) ∧
      Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase  := by sorry
