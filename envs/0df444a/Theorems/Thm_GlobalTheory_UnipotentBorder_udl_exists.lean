-- Prove2me | Theorems.Thm_GlobalTheory_UnipotentBorder_udl_exists
-- name    : GlobalTheory.UnipotentBorder.udl_exists
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:25:39.60881+00:00
-- url     : https://prove2.me/theorems/aedf6341-91de-491e-b869-19e0115a184d
-- title:
--   Unipotent Border: udl exists
-- statement:
--   The Unipotent Border construction uses the udl exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IwahoriFactorisation.lean#L174-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IwahoriFactorisation.lean#L174-L255

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnipotentBorder
open Matrix
variable {O : Type} [CommRing O]

theorem GlobalTheory.UnipotentBorder.udl_exists [IsLocalRing O] {α β : O} (hβ : ¬IsUnit β) :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O),
    (∀ i j, (i < j → α ∣ g i j) ∧ (j < i → β ∣ g i j)) → (∀ i, IsUnit (g i i)) →
    ∃ (U : Matrix (Fin n) (Fin n) O) (D : Fin n → Oˣ) (L : Matrix (Fin n) (Fin n) O),
      (∀ i j, (j < i → U i j = 0) ∧ (i = j → U i j = 1) ∧ (i < j → α ∣ U i j)) ∧
      (∀ i j, (i < j → L i j = 0) ∧ (i = j → L i j = 1) ∧ (j < i → β ∣ L i j)) ∧
      g = U * diagonal (fun i => (D i : O)) * L := by sorry
