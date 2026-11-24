-- Prove2me | Theorems.Thm_GlobalTheory_T_wittVector_dvd_of_mem_saturated_ideal
-- name    : GlobalTheory.T.wittVector_dvd_of_mem_saturated_ideal
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:01:01.009607+00:00
-- url     : https://prove2.me/theorems/7bacc356-ddad-4cbb-bfc0-90870038fae6
-- title:
--   T: witt Vector dvd of mem saturated ideal
-- statement:
--   The T construction uses the witt Vector dvd of mem saturated ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorDvdOfSaturatedIdealStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorDvdOfSaturatedIdealStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorDvdOfSaturatedIdeal
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorDvdOfSaturatedIdealStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.wittVector_dvd_of_mem_saturated_ideal : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [CharP R l] [PerfectRing R l] (J : Ideal (WittVector l R)) (μ : WittVector l R), μ ∈ J → (∀ a, (l : WittVector l R) * a ∈ J → a ∈ J) → (∀ a ∈ J, μ.coeff 0 ∣ a.coeff 0) → ∀ a ∈ J, μ ∣ a := by sorry
