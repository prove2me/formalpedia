-- Prove2me | Theorems.Thm_GlobalTheory_LevelExist_exists_isSymplecticFamily_span
-- name    : GlobalTheory.LevelExist.exists_isSymplecticFamily_span
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:03:36.473262+00:00
-- url     : https://prove2.me/theorems/7ecebd6e-6813-4867-a20c-2362dd68a2b7
-- title:
--   Level Exist: exists is Symplectic Family span
-- statement:
--   The Level Exist construction uses the exists is Symplectic Family span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsIsSymplecticFamilySpan.lean#L9-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsIsSymplecticFamilySpan.lean#L9-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsIsSymplecticFamilySpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.LevelExist

theorem GlobalTheory.LevelExist.exists_isSymplecticFamily_span {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [IsArtinian R V]
    {B : LinearMap.BilinForm R V} (hB : B.IsAlt) (t : R) (ht : ∀ r, t * r ≠ 0 → IsUnit r) (N : Submodule R V) :
    (∀ x ∈ N, (∀ y ∈ N, B x y = 0) → x = 0) →
    (∀ x ∈ N, x ≠ 0 → ∃ a : R, ∃ y ∈ N, a • x = t • y ∧ t • y ≠ 0) →
    ∃ (g : ℕ) (e f : Fin g → V), IsSymplecticFamily B e f (fun _ => 1) ∧
      Submodule.span R (Set.range (Sum.elim e f)) = N := by sorry
