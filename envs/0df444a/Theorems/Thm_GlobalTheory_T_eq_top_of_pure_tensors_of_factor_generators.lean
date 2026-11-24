-- Prove2me | Theorems.Thm_GlobalTheory_T_eq_top_of_pure_tensors_of_factor_generators
-- name    : GlobalTheory.T.eq_top_of_pure_tensors_of_factor_generators
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:32:37.546517+00:00
-- url     : https://prove2.me/theorems/c1f8ba93-c089-4f8b-bab9-3d183180c7b7
-- title:
--   T: eq top of pure tensors of factor generators
-- statement:
--   The T construction uses the eq top of pure tensors of factor generators property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EqTopOfPureTensorsOfFactorGeneratorsStatement.lean#L8-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EqTopOfPureTensorsOfFactorGeneratorsStatement.lean#L8-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EqTopOfPureTensorsOfFactorGenerators
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EqTopOfPureTensorsOfFactorGeneratorsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.eq_top_of_pure_tensors_of_factor_generators : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀]
    {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (Op₀ : Set (Module.End ℂ M₀)) (Op : ∀ i, Set (Module.End ℂ (M i)))
    (Rel₀ : Submodule ℂ M₀) (Rel : ∀ i, Submodule ℂ (M i)) (F₀ : Finset M₀) (F : ∀ i, Finset (M i)),
    (∀ N : Submodule ℂ M₀, Rel₀ ≤ N → GlobalTheory.TensHead.Stab Op₀ N → (↑F₀ : Set M₀) ⊆ ↑N → N = ⊤) →
    (∀ i, ∀ N : Submodule ℂ (M i), Rel i ≤ N → GlobalTheory.TensHead.Stab (Op i) N →
      (↑(F i) : Set (M i)) ⊆ ↑N → N = ⊤) →
    ∀ N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i)),
      (∀ x ∈ Rel₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N) →
      (∀ i, ∀ x ∈ Rel i, ∀ (x₀ : M₀) (y : ∀ j, M j),
        x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N) →
      GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ (GlobalTheory.TensHead.piOps Op)) N →
      (∀ x₀ ∈ F₀, ∀ y : ∀ i, M i, (∀ i, y i ∈ F i) → x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y ∈ N) →
      N = ⊤ := by sorry
