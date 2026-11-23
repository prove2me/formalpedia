-- Prove2me | Theorems.Thm_GlobalTheory_PerfectCompletion_eval_eq_zero_iff
-- name    : GlobalTheory.PerfectCompletion.eval_eq_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:05.757593+00:00
-- url     : https://prove2.me/theorems/3135c916-022f-45e0-8c35-1ce660b8b838
-- title:
--   Perfect Completion: eval eq zero iff
-- statement:
--   The Perfect Completion construction uses the eval eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdicCompletionPrincipalPerfect.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdicCompletionPrincipalPerfect.lean#L9-L19

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

theorem GlobalTheory.PerfectCompletion.eval_eq_zero_iff (n : ℕ) (y : AdicCompletion (Ideal.span {x}) V) :
    AdicCompletion.eval (Ideal.span {x}) V n y = 0 ↔
      (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ^ n ∣ y := by sorry
