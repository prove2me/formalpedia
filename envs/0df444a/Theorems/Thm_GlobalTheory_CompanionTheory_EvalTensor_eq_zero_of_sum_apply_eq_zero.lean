-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EvalTensor_eq_zero_of_sum_apply_eq_zero
-- name    : GlobalTheory.CompanionTheory.EvalTensor.eq_zero_of_sum_apply_eq_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:38:19.202961+00:00
-- url     : https://prove2.me/theorems/574ef839-ad7c-43f8-89a7-df4ee15db2b2
-- title:
--   Eval Tensor: eq zero of sum apply eq zero
-- statement:
--   The Eval Tensor construction uses the eq zero of sum apply eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EqZeroOfSumApplyEqZero.lean#L12-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EqZeroOfSumApplyEqZero.lean#L12-L95

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

theorem GlobalTheory.CompanionTheory.EvalTensor.eq_zero_of_sum_apply_eq_zero (σ : Representation ℂ G S) (π : Representation ℂ G V)
    (hirr : σ.IsIrreducible)
    (hschur : ∀ A : S →ₗ[ℂ] S, (∀ g s, A (σ g s) = σ g (A s)) → ∃ c : ℂ, A = c • LinearMap.id)
    {ι : Type} (b : ι → (S →ₗ[ℂ] V)) (hli : LinearIndependent ℂ b)
    (hb : ∀ i g s, b i (σ g s) = π g (b i s)) (J : Finset ι) :
    ∀ t : ι → S, ∑ j ∈ J, b j (t j) = 0 → ∀ j ∈ J, t j = 0 := by sorry
