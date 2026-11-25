-- Prove2me | Theorems.Thm_GlobalTheory_exists_isLocalHom_adicCompletion_extend
-- name    : GlobalTheory.exists_isLocalHom_adicCompletion_extend
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:45:35.205318+00:00
-- url     : https://prove2.me/theorems/e2e1bdf1-08e2-4741-bf07-d63c16a0043d
-- title:
--   Global Theory: exists is Local Hom adic Completion extend
-- statement:
--   The Global Theory construction uses the exists is Local Hom adic Completion extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIsLocalHomAdicCompletionExtend.lean#L7-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIsLocalHomAdicCompletionExtend.lean#L7-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsLocalHomAdicCompletionExtend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.exists_isLocalHom_adicCompletion_extend (O : Type) [CommRing O] [IsLocalRing O]
    [IsNoetherianRing O] (V : Type) [CommRing V] [IsLocalRing V]
    [IsAdicComplete (maximalIdeal V) V] (ψ : O →+* V) (hψ : IsLocalHom ψ) :
    ∃ ev₀ : AdicCompletion (maximalIdeal O) O →+* V,
      IsLocalHom ev₀ ∧ ∀ a, ev₀ (algebraMap O _ a) = ψ a := by sorry
