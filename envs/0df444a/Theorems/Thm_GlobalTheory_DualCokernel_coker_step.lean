-- Prove2me | Theorems.Thm_GlobalTheory_DualCokernel_coker_step
-- name    : GlobalTheory.DualCokernel.coker_step
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:26.847912+00:00
-- url     : https://prove2.me/theorems/417f184d-1298-4d7f-aadd-979c56413dd5
-- title:
--   Dual Cokernel: coker step
-- statement:
--   The Dual Cokernel construction uses the coker step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsSMulRegularCokerDualMapOfExactFibres.lean#L120-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsSMulRegularCokerDualMapOfExactFibres.lean#L120-L175

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function
open GlobalTheory
open GlobalTheory.DualCokernel
variable {R : Type} [CommRing R]
variable [IsLocalRing R]
variable [IsNoetherianRing R]

theorem GlobalTheory.DualCokernel.coker_step (ϖ : R) (hϖ : ϖ ∈ maximalIdeal R) {D₀ D₁ D₂ : Type}
    [AddCommGroup D₀] [Module R D₀] [AddCommGroup D₁] [Module R D₁] [AddCommGroup D₂] [Module R D₂]
    [Module.Finite R D₁] (β : D₂ →ₗ[R] D₁) (α : D₁ →ₗ[R] D₀) (hαβ : ∀ x, α (β x) = 0)
    (hD₀ : IsSMulRegular D₀ ϖ) (n : ℕ) (hE₀ : ∀ j < n + 1, ExtZero (R := R) D₀ j)
    (hQ : IsSMulRegular (D₁ ⧸ LinearMap.range β) ϖ)
    (hE : ∀ j < n + 2, ExtZero (R := R) (D₁ ⧸ LinearMap.range β) j)
    (h₁ : ∀ p : Ideal R, p.IsPrime → ϖ ∈ p → p ≠ maximalIdeal R →
      ∃ s, s ∉ p ∧ ∀ x, α x = 0 → s • x ∈ LinearMap.range β)
    (h₀ : ∀ p : Ideal R, p.IsPrime → ϖ ∈ p → p ≠ maximalIdeal R →
      ∃ s, s ∉ p ∧ ∀ x, ϖ • x ∈ LinearMap.range α → s • x ∈ LinearMap.range α) :
    IsSMulRegular (D₀ ⧸ LinearMap.range α) ϖ ∧
      ∀ j < n + 1, ExtZero (R := R) (D₀ ⧸ LinearMap.range α) j := by sorry
