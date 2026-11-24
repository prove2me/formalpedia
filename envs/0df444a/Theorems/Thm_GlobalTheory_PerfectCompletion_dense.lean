-- Prove2me | Theorems.Thm_GlobalTheory_PerfectCompletion_dense
-- name    : GlobalTheory.PerfectCompletion.dense
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:41:05.577029+00:00
-- url     : https://prove2.me/theorems/67d411d5-92b3-4126-bb6c-b657f9ef85de
-- title:
--   Perfect Completion: dense
-- statement:
--   The Perfect Completion construction uses the dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdicCompletionPrincipalPerfect.lean#L29-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdicCompletionPrincipalPerfect.lean#L29-L37

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

theorem GlobalTheory.PerfectCompletion.dense (y : AdicCompletion (Ideal.span {x}) V) (r : ℕ) :
    ∃ (s : V) (z : AdicCompletion (Ideal.span {x}) V),
      y = algebraMap V _ s + (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ^ r * z := by sorry
