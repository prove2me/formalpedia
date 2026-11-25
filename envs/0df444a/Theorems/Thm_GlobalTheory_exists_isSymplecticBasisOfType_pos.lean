-- Prove2me | Theorems.Thm_GlobalTheory_exists_isSymplecticBasisOfType_pos
-- name    : GlobalTheory.exists_isSymplecticBasisOfType_pos
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:45:23.614208+00:00
-- url     : https://prove2.me/theorems/cf2a1173-229b-53cd-8ea3-6f9de62d6283
-- title:
--   Global Theory: exists is Symplectic Basis Of Type pos
-- statement:
--   The Global Theory construction uses the exists is Symplectic Basis Of Type pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L441-L457
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L441-L457

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Function
open GlobalTheory
variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M]
  [Module R M] [Module.Free R M] [Module.Finite R M] {B : LinearMap.BilinForm R M}

theorem GlobalTheory.exists_isSymplecticBasisOfType_pos {M : Type*} [AddCommGroup M] [Module.Free ℤ M]
    [Module.Finite ℤ M] {B : LinearMap.BilinForm ℤ M} (hB : B.IsAlt) (hnd : Injective B) :
    ∃ (g : ℕ) (b : Basis (Fin g ⊕ Fin g) ℤ M) (d : Fin g → ℤ), IsSymplecticBasisOfType B b d ∧
      (∀ i, 0 < d i) ∧ ∀ i j, i ≤ j → d i ∣ d j := by sorry
