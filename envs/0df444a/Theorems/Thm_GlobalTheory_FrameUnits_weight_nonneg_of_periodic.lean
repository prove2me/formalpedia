-- Prove2me | Theorems.Thm_GlobalTheory_FrameUnits_weight_nonneg_of_periodic
-- name    : GlobalTheory.FrameUnits.weight_nonneg_of_periodic
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:39:21.859169+00:00
-- url     : https://prove2.me/theorems/33e8506c-b07a-446d-9426-9e891df24902
-- title:
--   Frame Units: weight nonneg of periodic
-- statement:
--   The Frame Units construction uses the weight nonneg of periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/TripleProductTorusPeriodicBounded.lean#L32-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/TripleProductTorusPeriodicBounded.lean#L32-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TripleProductTorusPeriodicBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open GlobalTheory.JetSer (IsNormRos primφ primε)
open GlobalTheory.CubeValues GlobalTheory.AppellHumbertTrivial
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.FrameUnits
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem GlobalTheory.FrameUnits.weight_nonneg_of_periodic {S : Set E} {R : ℝ} (hS : ∀ z, ∃ l ∈ S, ‖z + l‖ ≤ R)
    (r : E → ℂ) (hr : Differentiable ℂ r) (h0 : r 0 ≠ 0)
    (q : E → ℝ) (hq : Continuous q) (hs : ∀ (t : ℂ) v, q (t • v) = ‖t‖ ^ 2 * q v)
    (hp : ∀ l ∈ S, ∀ z, ‖r (z + l)‖ * Real.exp (-q (z + l)) = ‖r z‖ * Real.exp (-q z))
    (v : E) : 0 ≤ q v := by sorry
