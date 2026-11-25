-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isIrreducible_mGenQuotRep
-- name    : GroundTheory.Automorphic.RestrictedTensor.isIrreducible_mGenQuotRep
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:32:33.440799+00:00
-- url     : https://prove2.me/theorems/1c50b9a1-acce-48d4-8994-bd2fd61c75ca
-- title:
--   Restricted Tensor: is Irreducible m Gen Quot Rep
-- statement:
--   The Restricted Tensor construction uses the is Irreducible m Gen Quot Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L281-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L281-L349

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Module Set
variable {M : Type*} [Monoid M] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]
variable (ρ : Representation ℂ M V)
variable (e : End ℂ V) (N : Submodule ℂ V)
variable {ρ e N}

theorem GroundTheory.Automorphic.RestrictedTensor.isIrreducible_mGenQuotRep (he : IsWinProj ρ e) (hNe : N ≤ LinearMap.range e)
    (hNst : ∀ g, ∀ n ∈ N, e (ρ g n) ∈ N) (hN0 : N ≠ ⊥)
    (hNmin : ∀ N₁ : Submodule ℂ V, N₁ ≤ N → N₁ ≠ ⊥ → (∀ g, ∀ n ∈ N₁, e (ρ g n) ∈ N₁) → N₁ = N) :
    (mGenQuotRep ρ e N).IsIrreducible := by sorry
