-- Prove2me | Theorems.Thm_GlobalTheory_wittVector_dvd_of_saturated_ideal
-- name    : GlobalTheory.wittVector_dvd_of_saturated_ideal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:25:06.012022+00:00
-- url     : https://prove2.me/theorems/347d0b82-e18c-4de0-ace2-46b05f05e4bd
-- title:
--   Global Theory: witt Vector dvd of saturated ideal
-- statement:
--   The Global Theory construction uses the witt Vector dvd of saturated ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorDvdOfSaturatedIdeal.lean#L47-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorDvdOfSaturatedIdeal.lean#L47-L114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorDvdOfSaturatedIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WittVector

theorem GlobalTheory.wittVector_dvd_of_saturated_ideal : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R]
    [CharP R l] [PerfectRing R l] (J : Ideal (WittVector l R)) (μ : WittVector l R), μ ∈ J →
    (∀ a, (l : WittVector l R) * a ∈ J → a ∈ J) → (∀ a ∈ J, μ.coeff 0 ∣ a.coeff 0) →
    ∀ a ∈ J, μ ∣ a := by sorry
