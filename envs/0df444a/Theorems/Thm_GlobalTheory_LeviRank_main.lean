-- Prove2me | Theorems.Thm_GlobalTheory_LeviRank_main
-- name    : GlobalTheory.LeviRank.main
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:25:27.535806+00:00
-- url     : https://prove2.me/theorems/967ffd0f-fc77-4939-8094-41d494cce6bd
-- title:
--   Levi Rank: main
-- statement:
--   The Levi Rank construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsSelectForms.lean#L52-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsSelectForms.lean#L52-L108

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsSelectForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.L2DbarEstimates Topology
open scoped ContDiff Matrix
open GlobalTheory GlobalTheory.LeviRank

theorem GlobalTheory.LeviRank.main : ∀ (n N : ℕ) (w : Fin N → V n → ℂ) (U : Set (V n)), IsOpen U → (0 : V n) ∈ U →
    (∀ k, DifferentiableOn ℂ (w k) U) → (∃ k, w k 0 ≠ 0) →
    (∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < (leviV n (fun z => ((Real.log (∑ k, ‖w k z‖ ^ 2) : ℝ) : ℂ)) 0 ξ).re) →
    ∃ (j0 : Fin N) (jj : Fin n → Fin N), w j0 0 ≠ 0 ∧
      (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => w (jj k) z / w j0 z : V n)) 0).det ≠ 0 := by sorry
