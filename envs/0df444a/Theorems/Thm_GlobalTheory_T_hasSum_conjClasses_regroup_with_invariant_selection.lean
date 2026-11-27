-- Prove2me | Theorems.Thm_GlobalTheory_T_hasSum_conjClasses_regroup_with_invariant_selection
-- name    : GlobalTheory.T.hasSum_conjClasses_regroup_with_invariant_selection
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T05:55:16.503626+00:00
-- url     : https://prove2.me/theorems/1263c043-3b43-44e6-bdb4-06a369177389
-- title:
--   T: has Sum conj Classes regroup with invariant selection
-- statement:
--   The T construction uses the has Sum conj Classes regroup with invariant selection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumConjClassesRegroupWithInvariantSelectionStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumConjClassesRegroupWithInvariantSelectionStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumConjClassesRegroupWithInvariantSelection
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumConjClassesRegroupWithInvariantSelectionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hasSum_conjClasses_regroup_with_invariant_selection : ∀ {G : Type} [Group G] (g : G → ℂ), (Function.support g).Finite → ∀ (R P : G → Prop), (∀ δ, g δ ≠ 0 → R δ) → (∀ a b, IsConj a b → P a → P b) → HasSum (fun i : {𝔬 : Set G // ∃ γ, R γ ∧ 𝔬 = {δ | IsConj γ δ}} => ∑' δ : i.1, g δ) (∑' δ, g δ) ∧ HasSum (fun i : {𝔬 : Set G // ∃ γ, R γ ∧ 𝔬 = {δ | IsConj γ δ}} => {i : {𝔬 : Set G // ∃ γ, R γ ∧ 𝔬 = {δ | IsConj γ δ}} | ∀ δ ∈ i.1, P δ}.indicator (fun i => ∑' δ : i.1, g δ) i) (∑' δ : {δ // P δ}, g δ) := by sorry
