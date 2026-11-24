-- Prove2me | Theorems.Thm_GlobalTheory_exists_symplectic_coordinates_adapted
-- name    : GlobalTheory.exists_symplectic_coordinates_adapted
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:42:35.514019+00:00
-- url     : https://prove2.me/theorems/31339a9a-8e8f-4d9b-82a3-5e675346677d
-- title:
--   Global Theory: exists symplectic coordinates adapted
-- statement:
--   The Global Theory construction uses the exists symplectic coordinates adapted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsSymplecticCoordinatesAdapted.lean#L11-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsSymplecticCoordinatesAdapted.lean#L11-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsSymplecticCoordinatesAdapted
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
open Module Function

theorem GlobalTheory.exists_symplectic_coordinates_adapted {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ]
    [Module.Finite ℤ Λ] {ω : LinearMap.BilinForm ℤ Λ} (hω : ω.IsAlt) (hp : Bijective ω)
    {I : Submodule ℤ Λ} (hsat : ∀ (k : ℤ) (x : Λ), k ≠ 0 → k • x ∈ I → x ∈ I)
    (hiso : ∀ x ∈ I, ∀ y ∈ I, ω x y = 0) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ∃ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] Λ) (S : Finset (Fin g)),
      (∀ a b, ω (bas a) (bas b) = ε * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd a b) ∧
      I = Submodule.span ℤ ((fun k => bas (Pi.single (Sum.inl k) 1)) '' (S : Set (Fin g))) ∧
      2 * g = finrank ℤ Λ := by sorry
