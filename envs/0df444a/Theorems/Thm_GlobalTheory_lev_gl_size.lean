-- Prove2me | Theorems.Thm_GlobalTheory_lev_gl_size
-- name    : GlobalTheory.lev_gl_size
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:47:35.217517+00:00
-- url     : https://prove2.me/theorems/c574a5c6-464f-4894-96fa-b6f4e2111c45
-- title:
--   Global Theory: lev gl size
-- statement:
--   The Global Theory construction uses the lev gl size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UnitaryGlModuleLevelSumNormSqLe.lean#L11-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UnitaryGlModuleLevelSumNormSqLe.lean#L11-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CardFilterFinBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitaryGlModuleLevelOffDiagNormSqLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WeightNearDiagonalOperatorsBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitaryGlModuleLevelSumNormSqLe
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
open GlobalTheory

theorem GlobalTheory.lev_gl_size : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv b : ℝ) (w : M),
    IsMod ε E μ → Shape ε kk μ bv → bv ≤ b → j ≤ 4 * n ^ 2 → Lev ε E μ j w →
    ∑ a, ∑ c, ‖E a c w‖ ^ 2 ≤ b ^ 4 * ‖w‖ ^ 2 := by sorry
