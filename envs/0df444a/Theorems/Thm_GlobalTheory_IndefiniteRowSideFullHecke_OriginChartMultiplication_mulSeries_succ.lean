-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OriginChartMultiplication_mulSeries_succ
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication.mulSeries_succ
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:14:34.953496+00:00
-- url     : https://prove2.me/theorems/8c2df005-8e65-427f-b010-24ea766af0e0
-- title:
--   Origin Chart Multiplication: mul Series succ
-- statement:
--   The Origin Chart Multiplication construction uses the mul Series succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/OriginChartMultiplication.lean#L40-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/OriginChartMultiplication.lean#L40-L41

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication.mulSeries_succ {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) (n : ℕ) :
    mulSeries F (n + 1) = F.add (mulSeries F n) (pt R d 0) := by sorry
