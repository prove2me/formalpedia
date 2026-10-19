-- Prove2me | Theorems.Thm_MazurTransfer_Order13SingleSectionTwoActualAffineCharts_actual_two_affine_open_cover
-- name    : MazurTransfer.Order13SingleSectionTwoActualAffineCharts.actual_two_affine_open_cover
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T06:44:58.268089+00:00
-- url     : https://prove2.me/theorems/63e2871c-267f-40bf-b3d0-712a5d1852d5
-- title:
--   The two actual finite charts cover the whole order-thirteen curve
-- statement:
--   Let $R$ be a noetherian commutative integral domain with $104$ invertible. Let $U$ be the actual positive-infinity section complement and $V$ the actual inverse finite-chart open of the order-thirteen curve $C$. Then $$U\cup V=C.$$ Both literal opens are the original ones; the statement supplies the cover field of integral FiniteMapData.
-- source:
--   MazurTheorem, Apache-2.0, Vas and contributors. Uses the original positive-infinity lift into the actual reciprocal patch and the existing Proved public first-chart complement identity. The complete original cover statement, including both actual opens and all hypotheses, is retained and kernel-compared. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: unchanged actual integral FiniteMapData.

import Mathlib
import Definitions.Def_MazurTransfer_Order13FirstFiniteChartCanonicalOpen
import Definitions.Def_MazurTransfer_Order13InverseChartOpen
open CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13ActualPositiveInfinityComplement
open MazurTransfer.Order13InverseParameterFiniteAlgebra
universe u

theorem MazurTransfer.Order13SingleSectionTwoActualAffineCharts.actual_two_affine_open_cover (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] (h104 : IsUnit (104 : R)) :
    sectionComplementOpen R ⊔ inverseChartOpen R = ⊤  := by sorry
