-- Prove2me | Theorems.Thm_GlobalTheory_PerfectCompletion_dvd_iff
-- name    : GlobalTheory.PerfectCompletion.dvd_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:41:04.148042+00:00
-- url     : https://prove2.me/theorems/08750668-d5db-44b3-9ff0-d208f7993870
-- title:
--   Perfect Completion: dvd iff
-- statement:
--   The Perfect Completion construction uses the dvd iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdicCompletionPrincipalPerfect.lean#L39-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdicCompletionPrincipalPerfect.lean#L39-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionPrincipalPerfect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PerfectCompletion
variable {V : Type} [CommRing V] (x : V)

theorem GlobalTheory.PerfectCompletion.dvd_iff (s : V) (r : ℕ) :
    (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ^ r ∣ algebraMap V _ s ↔ x ^ r ∣ s := by sorry
