-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_Dens_exists_tmul_mem
-- name    : GlobalTheory.ThK.Dbl.Dens.exists_tmul_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:03:05.896524+00:00
-- url     : https://prove2.me/theorems/b9fc5d72-a865-4053-835d-11ff5c2cf596
-- title:
--   Dens: exists tmul mem
-- statement:
--   The Dens construction uses the exists tmul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/PairsD.lean#L141-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/PairsD.lean#L141-L251

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_PairsD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Dens
open Polynomial Cardinal

theorem GlobalTheory.ThK.Dbl.Dens.exists_tmul_mem {α : Type} [Finite α] [DecidableEq α] {A : Type} [AddCommGroup A]
    [Module ℂ A] {X : α → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (O : ∀ i, Set (Module.End ℂ (X i))) (hrank : ∀ i, Module.rank ℂ (X i) ≤ Cardinal.aleph0)
    (hnt : ∀ i, Nontrivial (X i))
    (hirr : ∀ i (N : Submodule ℂ (X i)), (∀ T ∈ O i, ∀ x ∈ N, T x ∈ N) → N = ⊥ ∨ N = ⊤)
    (N : Submodule ℂ (A ⊗[ℂ] PiTensorProduct ℂ X))
    (hN : ∀ i, ∀ T ∈ O i, ∀ x ∈ N, LinearMap.lTensor A (PiTensorProduct.map
      (Function.update (fun j => (LinearMap.id : X j →ₗ[ℂ] X j)) i T)) x ∈ N)
    (x : A ⊗[ℂ] PiTensorProduct ℂ X) (hxN : x ∈ N) (hx0 : x ≠ 0) :
    ∃ a₀ : A, a₀ ≠ 0 ∧ ∀ y, a₀ ⊗ₜ[ℂ] y ∈ N := by sorry
