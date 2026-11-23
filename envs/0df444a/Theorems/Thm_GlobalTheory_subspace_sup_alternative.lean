-- Prove2me | Theorems.Thm_GlobalTheory_subspace_sup_alternative
-- name    : GlobalTheory.subspace_sup_alternative
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:23.988852+00:00
-- url     : https://prove2.me/theorems/0d372727-79dd-4463-a0ee-8fd814f3c90e
-- title:
--   Global Theory: subspace sup alternative
-- statement:
--   The Global Theory construction uses the subspace sup alternative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/SubspaceSupAlternative.lean#L8-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/SubspaceSupAlternative.lean#L8-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_SubspaceSupAlternative
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory

theorem GlobalTheory.subspace_sup_alternative :
    (∀ (K V Y σ : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype σ] (r : ℕ) (t : σ → Y → Y) (D : Y → Submodule K V → ℝ) (α : ℕ → Y → ℝ) (c Ω : ℝ), Module.finrank K V = r → 1 ≤ Ω → (∀ y W, 0 < D y W) → (∀ i ≤ r, ∀ y, IsLUB (D y '' {W | Module.finrank K W = i}) (α i y)) → (∀ y W₁ W₂, D y W₁ * D y W₂ ≤ D y (W₁ ⊓ W₂) * D y (W₁ ⊔ W₂)) → (∀ s y W, D (t s y) W ≤ Ω * D y W ∧ D y W ≤ Ω * D (t s y) W) → (∀ y W, W ≠ ⊥ → W ≠ ⊤ → ∑ s, D (t s y) W ≤ Fintype.card σ * (c * D y W)) → ∃ C : ℝ, 0 ≤ C ∧ (∀ (y : Y) (i : ℕ), 0 < i → i < r → (∑ s, α i (t s y) ≤ Fintype.card σ * (c * α i y)) ∨ ∃ j : ℕ, 0 < j ∧ j ≤ i ∧ i + j ≤ r ∧ ∀ s, α i (t s y) ≤ C * Real.sqrt (α (i - j) y * α (i + j) y))) := by sorry
