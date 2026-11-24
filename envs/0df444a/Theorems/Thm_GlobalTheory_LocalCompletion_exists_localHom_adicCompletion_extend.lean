-- Prove2me | Theorems.Thm_GlobalTheory_LocalCompletion_exists_localHom_adicCompletion_extend
-- name    : GlobalTheory.LocalCompletion.exists_localHom_adicCompletion_extend
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:14:11.774119+00:00
-- url     : https://prove2.me/theorems/506bc7a1-e2a4-4cf5-9c20-72029dc1a223
-- title:
--   Local Completion: exists local Hom adic Completion extend
-- statement:
--   The Local Completion construction uses the exists local Hom adic Completion extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLocalHomAdicCompletionExtend.lean#L11-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLocalHomAdicCompletionExtend.lean#L11-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLocalHomAdicCompletionExtend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open IsLocalRing
open GlobalTheory GlobalTheory.LocalCompletion

theorem GlobalTheory.LocalCompletion.exists_localHom_adicCompletion_extend :
    ∀ (A R : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsLocalRing R],
      IsAdicComplete (maximalIdeal R) R → ∀ (φ : A →+* R), IsLocalHom φ →
      ∃ ψ : AdicCompletion (maximalIdeal A) A →+* R,
        IsLocalHom ψ ∧ ψ.comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) = φ := by sorry
