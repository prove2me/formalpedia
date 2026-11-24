-- Prove2me | Theorems.Thm_GlobalTheory_norm_hasSum_sub_finset_sum_le
-- name    : GlobalTheory.norm_hasSum_sub_finset_sum_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:13:26.373792+00:00
-- url     : https://prove2.me/theorems/f872858c-ba4d-4d2c-8fef-d8d42558f578
-- title:
--   Global Theory: norm has Sum sub finset sum le
-- statement:
--   The Global Theory construction uses the norm has Sum sub finset sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UltrametricNormHasSumSubFinsetSumLe.lean#L6-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UltrametricNormHasSumSubFinsetSumLe.lean#L6-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricNormHasSumSubFinsetSumLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.norm_hasSum_sub_finset_sum_le : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι : Type) (f : ι → K) (s : K) (I : Finset ι) (ε : ℝ), 0 ≤ ε → HasSum f s → (∀ i, i ∉ I → ‖f i‖ ≤ ε) → ‖s - ∑ i ∈ I, f i‖ ≤ ε := by sorry
