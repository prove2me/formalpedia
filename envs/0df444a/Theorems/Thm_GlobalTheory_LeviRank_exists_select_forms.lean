-- Prove2me | Theorems.Thm_GlobalTheory_LeviRank_exists_select_forms
-- name    : GlobalTheory.LeviRank.exists_select_forms
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:47:57.968615+00:00
-- url     : https://prove2.me/theorems/bcbd1cbb-3ba9-4fd4-b623-02e954522b91
-- title:
--   Levi Rank: exists select forms
-- statement:
--   The Levi Rank construction uses the exists select forms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsSelectForms.lean#L12-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsSelectForms.lean#L12-L39

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

theorem GlobalTheory.LeviRank.exists_select_forms {K M : Type} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] {n N : ℕ} (hn : Module.finrank K M = n)
    (φ : Fin N → Module.Dual K M) (hφ : ∀ x, (∀ k, φ k x = 0) → x = 0) :
    ∃ jj : Fin n → Fin N, ∀ x, (∀ k, φ (jj k) x = 0) → x = 0 := by sorry
