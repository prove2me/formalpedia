-- Prove2me | Theorems.Thm_GlobalTheory_T_finiteDimensional_span_adjoin_apply_of_annihilating
-- name    : GlobalTheory.T.finiteDimensional_span_adjoin_apply_of_annihilating
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:31:07.335097+00:00
-- url     : https://prove2.me/theorems/71caea8a-7ebd-511f-9e08-9b233b111680
-- title:
--   T: finite Dimensional span adjoin apply of annihilating
-- statement:
--   The T construction uses the finite Dimensional span adjoin apply of annihilating property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalSpanAdjoinStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalSpanAdjoinStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAdjoin
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAdjoinStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finiteDimensional_span_adjoin_apply_of_annihilating : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (c : ℕ → Module.End ℂ V) (g : ℂ → Module.End ℂ V), (∀ u, g u = ∑ i ∈ Finset.range (n + 1), u ^ i • c i) → (∀ u u', Commute (g u) (g u')) → ∀ (w : V) (P : ℂ → Polynomial ℂ), (∀ u, P u ≠ 0) → (∀ u, Polynomial.aeval (g u) (P u) w = 0) → FiniteDimensional ℂ (Submodule.span ℂ {y | ∃ b ∈ Algebra.adjoin ℂ (Set.range g), y = b w}) := by sorry
