-- Prove2me | Theorems.Thm_GlobalTheory_T_ultrametric_norm_hasSum_sub_finset_sum_le
-- name    : GlobalTheory.T.ultrametric_norm_hasSum_sub_finset_sum_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:48.227803+00:00
-- url     : https://prove2.me/theorems/e4d49956-0dc2-4b5f-8a31-12ae0f347cc4
-- title:
--   T: ultrametric norm has Sum sub finset sum le
-- statement:
--   The T construction uses the ultrametric norm has Sum sub finset sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UltrametricNormHasSumSubFinsetSumLeStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UltrametricNormHasSumSubFinsetSumLeStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricNormHasSumSubFinsetSumLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricNormHasSumSubFinsetSumLeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.ultrametric_norm_hasSum_sub_finset_sum_le : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι : Type) (f : ι → K) (s : K) (I : Finset ι) (ε : ℝ), 0 ≤ ε → HasSum f s → (∀ i, i ∉ I → ‖f i‖ ≤ ε) → ‖s - ∑ i ∈ I, f i‖ ≤ ε := by sorry
