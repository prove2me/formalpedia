-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticBasis_orthogonal_eq_span
-- name    : GlobalTheory.IsSymplecticBasis.orthogonal_eq_span
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:11:23.272277+00:00
-- url     : https://prove2.me/theorems/534457d2-0767-4290-9495-875331197ec9
-- title:
--   Is Symplectic Basis: orthogonal eq span
-- statement:
--   The Is Symplectic Basis construction uses the orthogonal eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L649-L672
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L649-L672

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

theorem GlobalTheory.IsSymplecticBasis.orthogonal_eq_span {ι κ : Type*} [Finite ι] [Finite κ]
    {b : Basis ((ι ⊕ κ) ⊕ (ι ⊕ κ)) R M} (hb : IsSymplecticBasis B b) {v : Basis ι R I}
    (hv : ∀ i, b (Sum.inl (Sum.inl i)) = v i) :
    B.orthogonal I = Submodule.span R
      (Set.range (fun i => b (Sum.inl i)) ∪ Set.range fun k => b (Sum.inr (Sum.inr k))) := by sorry
