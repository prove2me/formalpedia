-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EvalTensor_lift_flip_subtype_injective
-- name    : GlobalTheory.CompanionTheory.EvalTensor.lift_flip_subtype_injective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:38:12.838052+00:00
-- url     : https://prove2.me/theorems/a064c95c-c186-42c9-9bce-e8b5a15bb250
-- title:
--   Eval Tensor: lift flip subtype injective
-- statement:
--   The Eval Tensor construction uses the lift flip subtype injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EqZeroOfSumApplyEqZero.lean#L97-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EqZeroOfSumApplyEqZero.lean#L97-L118

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EqZeroOfSumApplyEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EvalTensor
variable {G S V : Type} [Group G] [AddCommGroup S] [Module ℂ S] [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CompanionTheory.EvalTensor.lift_flip_subtype_injective : ∀ {G S V : Type} [Group G] [AddCommGroup S] [Module ℂ S] [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ G S) (π : Representation ℂ G V), σ.IsIrreducible → (∀ A : S →ₗ[ℂ] S, (∀ g s, A (σ g s) = σ g (A s)) → ∃ c : ℂ, A = c • LinearMap.id) → ∀ M : Submodule ℂ (S →ₗ[ℂ] V), (∀ f ∈ M, ∀ g s, f (σ g s) = π g (f s)) → Function.Injective (TensorProduct.lift (LinearMap.flip (M.subtype)) : S ⊗[ℂ] M →ₗ[ℂ] V) := by sorry
