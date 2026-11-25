-- Prove2me | Theorems.Thm_GlobalTheory_exists_isUnit_sub_of_ringHom_ne
-- name    : GlobalTheory.exists_isUnit_sub_of_ringHom_ne
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:50:18.902856+00:00
-- url     : https://prove2.me/theorems/2130a4db-4c21-417b-b34a-ba74d945c705
-- title:
--   Global Theory: exists is Unit sub of ring Hom ne
-- statement:
--   The Global Theory construction uses the exists is Unit sub of ring Hom ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsIsUnitSubOfRingHomNe.lean#L5-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsIsUnitSubOfRingHomNe.lean#L5-L80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsIsUnitSubOfRingHomNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_isUnit_sub_of_ringHom_ne : ∀ (A O : Type) [CommRing A] [Module.Finite ℤ A] [CommRing O] [IsLocalRing O] (g : ℕ), g.Prime → ¬ IsUnit (g : O) → (∀ x : A, x ^ g - x ∈ Ideal.span {(g : A)}) → ∀ σ σ' : A →+* O, σ ≠ σ' → ∃ a : A, IsUnit (σ a - σ' a) := by sorry
