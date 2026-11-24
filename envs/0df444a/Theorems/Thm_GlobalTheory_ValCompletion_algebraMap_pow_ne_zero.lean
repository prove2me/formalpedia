-- Prove2me | Theorems.Thm_GlobalTheory_ValCompletion_algebraMap_pow_ne_zero
-- name    : GlobalTheory.ValCompletion.algebraMap_pow_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:50:16.579799+00:00
-- url     : https://prove2.me/theorems/1e9690d8-da17-46da-8e55-750f7a95f526
-- title:
--   Val Completion: algebra Map pow ne zero
-- statement:
--   The Val Completion construction uses the algebra Map pow ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdicCompletionValuationRingCompleteValuationDoma.lean#L79-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdicCompletionValuationRingCompleteValuationDoma.lean#L79-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionValuationRingCompleteValuationDoma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory GlobalTheory.ValCompletion
variable {V : Type} [CommRing V] [IsDomain V] [ValuationRing V] {x : V}

theorem GlobalTheory.ValCompletion.algebraMap_pow_ne_zero (hx0 : x ≠ 0) (hxu : ¬ IsUnit x) (m : ℕ) : (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ^ m ≠ 0 := by sorry
