-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ModuleReduction_exists_reduction
-- name    : GlobalTheory.CompanionTheory.ModuleReduction.exists_reduction
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:01:48.373084+00:00
-- url     : https://prove2.me/theorems/d407c2e9-c531-44c0-9ef5-218b614b6570
-- title:
--   Module Reduction: exists reduction
-- statement:
--   The Module Reduction construction uses the exists reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/MemSmulOfTmulEqZero.lean#L34-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/MemSmulOfTmulEqZero.lean#L34-L102

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_MemSmulOfTmulEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct ChangeOfRings
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ModuleReduction

theorem GlobalTheory.CompanionTheory.ModuleReduction.exists_reduction (A O : Type) [CommRing A] [CommRing O] (θ : A →+* O)
    (hθ : Function.Surjective θ) (ξ : A) (hker : RingHom.ker θ = Ideal.span {ξ})
    (𝒞 : Type 1) [CategoryTheory.Category.{0} 𝒞] (M : CategoryTheory.Functor 𝒞 (ModuleCat.{0} A)) :
    ∃ (D : CategoryTheory.Functor 𝒞 (ModuleCat.{0} O)) (r : ∀ X : 𝒞, M.obj X →ₛₗ[θ] D.obj X),
      (∀ X, Function.Surjective (r X) ∧ ∀ m, r X m = 0 ↔ ∃ n, m = ξ • n) ∧
      ∀ (X Y : 𝒞) (f : X ⟶ Y) (m : M.obj X), D.map f (r X m) = r Y (M.map f m) := by sorry
