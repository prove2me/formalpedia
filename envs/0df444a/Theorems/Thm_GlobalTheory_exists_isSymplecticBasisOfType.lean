-- Prove2me | Theorems.Thm_GlobalTheory_exists_isSymplecticBasisOfType
-- name    : GlobalTheory.exists_isSymplecticBasisOfType
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:33:09.248706+00:00
-- url     : https://prove2.me/theorems/d806498b-e36c-425b-8ac5-d6f4570f8e19
-- title:
--   Global Theory: exists is Symplectic Basis Of Type
-- statement:
--   The Global Theory construction uses the exists is Symplectic Basis Of Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L433-L439
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L433-L439

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

theorem GlobalTheory.exists_isSymplecticBasisOfType (hB : B.IsAlt) (hnd : Injective B) :
    ∃ (g : ℕ) (b : Basis (Fin g ⊕ Fin g) R M) (d : Fin g → R), IsSymplecticBasisOfType B b d ∧
      (∀ i, d i ≠ 0) ∧ ∀ i j, i ≤ j → d i ∣ d j := by sorry
