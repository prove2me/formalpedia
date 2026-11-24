-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OriginChartMultiplication_constantCoeff_mulSeries
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication.constantCoeff_mulSeries
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:14:10.997797+00:00
-- url     : https://prove2.me/theorems/5e095653-9ddd-4b38-960e-8e0684983053
-- title:
--   Origin Chart Multiplication: constant Coeff mul Series
-- statement:
--   The Origin Chart Multiplication construction uses the constant Coeff mul Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/OriginChartMultiplication.lean#L48-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/OriginChartMultiplication.lean#L48-L60

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication.constantCoeff_mulSeries {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) (n : ℕ)
    (i : Fin d) : MvPowerSeries.constantCoeff (mulSeries F n i) = 0 := by sorry
