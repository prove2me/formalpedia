-- Prove2me | Theorems.Thm_GlobalTheory_RegularCompletionPackage_exists_regular_completion
-- name    : GlobalTheory.RegularCompletionPackage.exists_regular_completion
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:05:19.722275+00:00
-- url     : https://prove2.me/theorems/6e236bd9-265c-4790-b229-47306c63dd15
-- title:
--   Regular Completion Package: exists regular completion
-- statement:
--   The Regular Completion Package construction uses the exists regular completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRegularCompletionFlat.lean#L9-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRegularCompletionFlat.lean#L9-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNoetherianRingAdicCompletionOfNoetherian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsRegularLocalRingAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularCompletionFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.RegularCompletionPackage

theorem GlobalTheory.RegularCompletionPackage.exists_regular_completion :
    ∀ (R₁ Ω : Type) [CommRing R₁] [IsRegularLocalRing R₁] [Field Ω] (u : R₁ →+* Ω),
      RingHom.ker u = maximalIdeal R₁ →
      ∃ (C : Type) (_ : CommRing C) (_ : IsRegularLocalRing C) (c : R₁ →+* C) (uC : C →+* Ω),
        c.Flat ∧ (maximalIdeal R₁).map c = maximalIdeal C ∧ IsAdicComplete (maximalIdeal C) C ∧
        RingHom.ker uC = maximalIdeal C ∧ uC.comp c = u := by sorry
