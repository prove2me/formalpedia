-- Prove2me | Theorems.Thm_GlobalTheory_CharForm_exists_periodic
-- name    : GlobalTheory.CharForm.exists_periodic
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:07:16.988137+00:00
-- url     : https://prove2.me/theorems/32cd3afb-c62d-4fbb-b0b1-a567d38f5509
-- title:
--   Char Form: exists periodic
-- statement:
--   The Char Form construction uses the exists periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEqMulApplyZero.lean#L31-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEqMulApplyZero.lean#L31-L62

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

theorem GlobalTheory.CharForm.exists_periodic {C : Set (X → ℂ)}
    (H : ∀ N ∈ 𝓝 (0 : X), ∃ U : AddSubgroup X, IsOpen (U : Set X) ∧ IsCompact (U : Set X) ∧ (U : Set X) ⊆ N ∧
      ∀ x₀ ∉ U, ∃ χ ∈ C, (∀ u ∈ U, χ (x₀ + u) = χ x₀) ∧ χ x₀ ≠ 1)
    {g : X → ℂ} (hg : g ∈ SB X) {V : Set X} (hV : V ∈ 𝓝 (0 : X)) :
    ∃ U : AddSubgroup X, IsOpen (U : Set X) ∧ IsCompact (U : Set X) ∧ (U : Set X) ⊆ V ∧
      (∀ x₀ ∉ U, ∃ χ ∈ C, (∀ u ∈ U, χ (x₀ + u) = χ x₀) ∧ χ x₀ ≠ 1) ∧ ∀ x, ∀ u ∈ U, g (x + u) = g x := by sorry
