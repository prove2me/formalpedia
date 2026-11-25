-- Prove2me | Theorems.Thm_GlobalTheory_T_unitaryGl_projection_level_sum_sq_le
-- name    : GlobalTheory.T.unitaryGl_projection_level_sum_sq_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:48:50.944845+00:00
-- url     : https://prove2.me/theorems/bac6f156-c8ae-4dc9-8d21-7fc462b7abed
-- title:
--   T: unitary Gl projection level sum sq le
-- statement:
--   The T construction uses the unitary Gl projection level sum sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UnitaryGlProjectionLevelSumSqLeStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UnitaryGlProjectionLevelSumSqLeStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitaryGlProjectionLevelSumSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitaryGlProjectionLevelSumSqLeStatement
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

theorem GlobalTheory.T.unitaryGl_projection_level_sum_sq_le : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr → Shape ε kk μ bv → j ≤ 4 * n ^ 2 → Lev ε E μ j w → ∀ c, (∀ s, Lev ε (F s) (μ - Pi.single s 1) (j + 2) (pr s (Pi.single c w))) ∧ ∑ s, ‖pr s (Pi.single c w)‖ ^ 2 ≤ (6 * bv) ^ (2 * (n + 1 - kk)) * ‖w‖ ^ 2 := by sorry
