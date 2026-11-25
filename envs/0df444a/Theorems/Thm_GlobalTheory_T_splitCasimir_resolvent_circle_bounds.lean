-- Prove2me | Theorems.Thm_GlobalTheory_T_splitCasimir_resolvent_circle_bounds
-- name    : GlobalTheory.T.splitCasimir_resolvent_circle_bounds
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:46:10.447842+00:00
-- url     : https://prove2.me/theorems/a26d508a-fe9b-54f0-aece-064c9ceeed8b
-- title:
--   T: split Casimir resolvent circle bounds
-- statement:
--   The T construction uses the split Casimir resolvent circle bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SplitCasimirResolventCircleBoundsStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SplitCasimirResolventCircleBoundsStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasimirResolventCircleBounds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasimirResolventCircleBoundsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.splitCasimir_resolvent_circle_bounds : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (x : Fin n → M), IsMod ε E μ → Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → (∀ c, Lev ε E μ j (x c)) → (∀ ζ : ℂ, ‖ζ + ((bv / 16 : ℝ) : ℂ)‖ = 9 * bv / 16 → (13 * bv / 32) ^ 2 * ∑ c, ‖x c‖ ^ 2 ≤ ∑ c, ‖ζ • x c - splitCas E x c‖ ^ 2) ∧ ∑ c, ‖splitCas E x c‖ ^ 2 ≤ (3 * bv) ^ 2 * ∑ c, ‖x c‖ ^ 2 := by sorry
