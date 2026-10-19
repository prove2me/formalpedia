-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualIntegralPicardChartSections_actual_hasChartSections
-- name    : MazurTransfer.Order13ActualIntegralPicardChartSections.actual_hasChartSections
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T04:47:50.717254+00:00
-- url     : https://prove2.me/theorems/dff2377e-1004-4d1a-a55c-b30f664c1224
-- title:
--   The actual integral order-thirteen curve has genus-two Picard chart sections
-- statement:
--   Let $R$ be a commutative ring in which $104$ is a unit. For the actual order-thirteen curve over $R$, the specified family of $216$ ordered triples of the six marked sections satisfies the Picard chart-section condition with genus $g=2$ and divisor degree $r=5$. Thus on every algebraically closed geometric fibre and for every degree-five divisor $D$, some indexed triple cuts its Riemann–Roch space to dimension one: $$\ell(D-P_1-P_2-P_3)=1.$$ This supplies the chart-section hypothesis in the actual integral degree-zero Picard representation theorem. The finite-map-data hypothesis is a separate construction.
-- source:
--   Unchanged statement and direct proof body from checked MazurTheorem Order13ActualIntegralPicardChartSections.lean. The actualTripleFamily constructor is the unchanged public constructor; the proof directly reuses the three public Proved inputs: six-section Picard chart criterion, field-point distinctness of the six actual sections, and actual geometric-fibre genus-two Riemann–Roch models. Complete original and public types are compared by closed kernel witnesses; the preamble is checked independently. Original per-file attribution and Apache-2.0 are retained. Vas and contributors.

import Definitions.Def_MazurTransfer_Order13ActualPicardTripleFamily
import Theorems.Thm_MazurTransfer_SixSectionPicardChartCriterion_hasChartSections_of_six_sections
import Theorems.Thm_MazurTransfer_Order13SixMarkedSectionsDistinct_six_sections_field_precomposition_injective
import Theorems.Thm_MazurTransfer_Order13GeometricFibreGenusTwoModels_geometric_fibre_genus_two_models
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13IntegralSections MazurTransfer.SixSectionPicardChartCriterion
open MazurTransfer.Order13ActualIntegralPicardChartSections
open MazurTransfer

theorem MazurTransfer.Order13ActualIntegralPicardChartSections.actual_hasChartSections (R : Type u) [CommRing R]  (h104 : IsUnit (104 : R)) :
    HasChartSections (curveToBase R) (g := 2) (r := 5) (actualTripleFamily R)  := by sorry
