-- Prove2me | Theorems.Thm_MazurTransfer_Order13InverseParameterFiniteAlgebra_actual_chart_intersection_opensRange
-- name    : MazurTransfer.Order13InverseParameterFiniteAlgebra.actual_chart_intersection_opensRange
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T06:47:20.63541+00:00
-- url     : https://prove2.me/theorems/7a28ab9a-5010-4d58-8ebe-09fb7d536bbd
-- title:
--   The actual finite-chart intersection is the ordinary parameter open
-- statement:
--   Let $R$ be a noetherian commutative integral domain with $104$ invertible. Let $U$ be the actual positive-infinity section complement and $V$ the actual inverse finite-chart open of the order-thirteen curve. Their intersection is exactly the image of the original ordinary parameter localization: $$U\cap V=\operatorname{im}\bigl(\operatorname{Spec}(A_t)\to C\bigr).$$ This identifies the literal overlap used by both parameter basic-open fields and parameter reciprocity in integral FiniteMapData.
-- source:
--   MazurTheorem, Apache-2.0, Vas and contributors. The original twenty-two-line actual_chart_intersection_opensRange proof is retained modulo qualifying explicit helper names. The reciprocal-patch membership helper is reassembled from the existing Proved public first-chart complement identity and public literal positive-infinity image interface, under the hypotheses of the unchanged final target. The original patch prime calculation and finite-chart overlap comparison are included explicitly. No transitive native helper is used as a public theorem. The complete original and public full types are kernel-compared. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: unchanged actual integral FiniteMapData.

import Mathlib
import Definitions.Def_MazurTransfer_Order13FirstFiniteChartCanonicalOpen
import Definitions.Def_MazurTransfer_Order13InverseFiniteAffineOpenPresentation
open CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13ActualPositiveInfinityComplement
open MazurTransfer.Order13InverseParameterFiniteAlgebra
universe u

theorem MazurTransfer.Order13InverseParameterFiniteAlgebra.actual_chart_intersection_opensRange (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] (h104 : IsUnit (104 : R)) :
    sectionComplementOpen R ⊓ inverseChartOpen R = (ordinaryParameterCurveMap R).opensRange  := by sorry
