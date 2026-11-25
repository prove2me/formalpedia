-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_regular_completion_flat
-- name    : GlobalTheory.T.exists_regular_completion_flat
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:30:49.354533+00:00
-- url     : https://prove2.me/theorems/c5415932-7fcc-46e4-b400-6e0ae9104f3c
-- title:
--   T: exists regular completion flat
-- statement:
--   The T construction uses the exists regular completion flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRegularCompletionFlatStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRegularCompletionFlatStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularCompletionFlat
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularCompletionFlatStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_regular_completion_flat : ∀ (R₁ Ω : Type) [CommRing R₁] [IsRegularLocalRing R₁] [Field Ω] (u : R₁ →+* Ω), RingHom.ker u = maximalIdeal R₁ → ∃ (C : Type) (_ : CommRing C) (_ : IsRegularLocalRing C) (c : R₁ →+* C) (uC : C →+* Ω), c.Flat ∧ (maximalIdeal R₁).map c = maximalIdeal C ∧ IsAdicComplete (maximalIdeal C) C ∧ RingHom.ker uC = maximalIdeal C ∧ uC.comp c = u := by sorry
