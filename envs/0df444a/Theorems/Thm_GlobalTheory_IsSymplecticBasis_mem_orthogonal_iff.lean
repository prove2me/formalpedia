-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticBasis_mem_orthogonal_iff
-- name    : GlobalTheory.IsSymplecticBasis.mem_orthogonal_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:45.562046+00:00
-- url     : https://prove2.me/theorems/492a8898-ef22-4cfa-bb7f-f8a3b21a658c
-- title:
--   Is Symplectic Basis: mem orthogonal iff
-- statement:
--   The Is Symplectic Basis construction uses the mem orthogonal iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L634-L645
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L634-L645

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
  [Module R M] [Module.Finite R M] {B : LinearMap.BilinForm R M} {I : Submodule R M}
omit [IsDomain R] [IsPrincipalIdealRing R] [Module.Finite R M]

theorem GlobalTheory.IsSymplecticBasis.mem_orthogonal_iff {ι κ : Type*} [Finite ι] [Finite κ]
    {b : Basis ((ι ⊕ κ) ⊕ (ι ⊕ κ)) R M} (hb : IsSymplecticBasis B b) {v : Basis ι R I}
    (hv : ∀ i, b (Sum.inl (Sum.inl i)) = v i) (x : M) :
    x ∈ B.orthogonal I ↔ ∀ i, b.repr x (Sum.inr (Sum.inl i)) = 0 := by sorry
