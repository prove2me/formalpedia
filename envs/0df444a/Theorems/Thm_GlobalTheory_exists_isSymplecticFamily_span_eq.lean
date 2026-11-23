-- Prove2me | Theorems.Thm_GlobalTheory_exists_isSymplecticFamily_span_eq
-- name    : GlobalTheory.exists_isSymplecticFamily_span_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:51.061821+00:00
-- url     : https://prove2.me/theorems/e70e4fd5-54f1-4005-bea2-7327b7ed16d1
-- title:
--   Global Theory: exists is Symplectic Family span eq
-- statement:
--   The Global Theory construction uses the exists is Symplectic Family span eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L163-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L163-L260

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
  [Module R M]

theorem GlobalTheory.exists_isSymplecticFamily_span_eq [Module.Free R M] [Module.Finite R M]
    {B : LinearMap.BilinForm R M} (hB : B.IsAlt) (N : Submodule R M)
    (hN : ∀ x ∈ N, (∀ y ∈ N, B x y = 0) → x = 0) :
    ∃ (g : ℕ) (e f : Fin g → M) (d : Fin g → R), IsSymplecticFamily B e f d ∧ (∀ i, d i ≠ 0) ∧
      (∀ i j, i ≤ j → d i ∣ d j) ∧ Submodule.span R (Set.range (Sum.elim e f)) = N := by sorry
