-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticFamily_exists_isSymplecticBasis
-- name    : GlobalTheory.IsSymplecticFamily.exists_isSymplecticBasis
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:50.946092+00:00
-- url     : https://prove2.me/theorems/3bdf8e33-0246-4196-8e8c-73e53d48b2ec
-- title:
--   Is Symplectic Family: exists is Symplectic Basis
-- statement:
--   The Is Symplectic Family construction uses the exists is Symplectic Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L410-L424
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L410-L424

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
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {B : LinearMap.BilinForm R M}

theorem GlobalTheory.IsSymplecticFamily.exists_isSymplecticBasis [IsDomain R] [Finite ι] {e f : ι → M}
    {d : ι → R} (h : IsSymplecticFamily B e f d) (hd : ∀ i, d i ≠ 0)
    (hspan : Submodule.span R (Set.range (Sum.elim e f)) = ⊤) (hp : Surjective B) :
    ∃ b : Basis (ι ⊕ ι) R M, IsSymplecticBasis B b ∧ ∀ i, b (Sum.inl i) = e i := by sorry
