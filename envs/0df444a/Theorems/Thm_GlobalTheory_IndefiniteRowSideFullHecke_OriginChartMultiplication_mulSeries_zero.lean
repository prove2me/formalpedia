-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OriginChartMultiplication_mulSeries_zero
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication.mulSeries_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:01.009405+00:00
-- url     : https://prove2.me/theorems/2a9d1e9a-bf1f-4f71-afa7-fd2f81b832ac
-- title:
--   Origin Chart Multiplication: mul Series zero
-- statement:
--   The Origin Chart Multiplication construction uses the mul Series zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/OriginChartMultiplication.lean#L38-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/OriginChartMultiplication.lean#L38-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_OriginChartMultiplication
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication

theorem GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication.mulSeries_zero {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) : mulSeries F 0 = 0 := by sorry
