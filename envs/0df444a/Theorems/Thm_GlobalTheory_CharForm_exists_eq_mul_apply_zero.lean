-- Prove2me | Theorems.Thm_GlobalTheory_CharForm_exists_eq_mul_apply_zero
-- name    : GlobalTheory.CharForm.exists_eq_mul_apply_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:58:13.1551+00:00
-- url     : https://prove2.me/theorems/b2546040-c16b-405f-9604-0fe4dc9b932b
-- title:
--   Char Form: exists eq mul apply zero
-- statement:
--   The Char Form construction uses the exists eq mul apply zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEqMulApplyZero.lean#L116-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEqMulApplyZero.lean#L116-L132

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEqMulApplyZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM
noncomputable section
open scoped Classical Topology
open GlobalTheory GlobalTheory.CharForm
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]

theorem GlobalTheory.CharForm.exists_eq_mul_apply_zero : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (C : Set (X → ℂ)),
    (∀ N ∈ nhds (0 : X), ∃ U : AddSubgroup X, IsOpen (U : Set X) ∧ IsCompact (U : Set X) ∧ (U : Set X) ⊆ N ∧
      ∀ x₀ ∉ U, ∃ χ ∈ C, (∀ u ∈ U, χ (x₀ + u) = χ x₀) ∧ χ x₀ ≠ 1) →
    ∀ (a : (X → ℂ) →ₗ[ℂ] ℂ), (∀ χ ∈ C, ∀ g ∈ SB X, a (fun x => χ x * g x) = a g) →
      ∃ c : ℂ, ∀ g ∈ SB X, a g = c * g 0 := by sorry
