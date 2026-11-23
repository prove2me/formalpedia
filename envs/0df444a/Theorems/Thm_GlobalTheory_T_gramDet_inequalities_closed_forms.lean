-- Prove2me | Theorems.Thm_GlobalTheory_T_gramDet_inequalities_closed_forms
-- name    : GlobalTheory.T.gramDet_inequalities_closed_forms
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:48:20.457217+00:00
-- url     : https://prove2.me/theorems/d7618341-91c3-42fe-ae21-b60cfa301b06
-- title:
--   T: gram Det inequalities closed forms
-- statement:
--   The T construction uses the gram Det inequalities closed forms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/GramDetInequalitiesClosedFormsStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/GramDetInequalitiesClosedFormsStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetInequalitiesClosedForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetInequalitiesClosedFormsStatement
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

theorem GlobalTheory.T.gramDet_inequalities_closed_forms : (∀ (m α β γ : Type) [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] (M : Matrix m (α ⊕ β ⊕ γ) ℂ), (((M.submatrix id (Sum.inl : α → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.inl : α → α ⊕ β ⊕ γ))).det.re) * (((M)ᴴ * (M)).det.re) ≤ (((M.submatrix id (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ))).det.re) * (((M.submatrix id (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ))).det.re)) ∧ (∀ (r : ℕ) (a : Matrix (Fin r) (Fin r) ℂ), ∃ ω : ℝ, 1 ≤ ω ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix (Fin r) ι ℂ), (((a * M)ᴴ * (a * M)).det.re) ≤ ω * (((M)ᴴ * (M)).det.re)) ∧ (∀ (r : ℕ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∃ δ c ω : ℝ, 0 < δ ∧ 0 ≤ c ∧ c < 1 ∧ 1 ≤ ω ∧ ∀ (i : ℕ) (M : Matrix (Fin r) (Fin i) ℂ), 0 < (((M)ᴴ * (M)).det.re) → (∀ a ∈ S, (((a * M)ᴴ * (a * M)).det.re) ≤ ω * (((M)ᴴ * (M)).det.re) ∧ (((M)ᴴ * (M)).det.re) ≤ ω * (((a * M)ᴴ * (a * M)).det.re)) ∧ (0 < i → i < r → ∑ a ∈ S, ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) ^ (-δ) ≤ S.card * c)) ∧ (∀ (r p : ℕ), 0 < p → p < r → ∃ S : Finset (Matrix (Fin r) (Fin r) ℂ), S.Nonempty ∧ (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) ∧ (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) ∧ ∀ a ∈ S, (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) ∧ ∃ s : Matrix (Fin r) (Fin r) ℂ, (s)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) * (s).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) ∧ s * a = a⁻¹ * s) := by sorry
