-- Prove2me | Theorems.Thm_GlobalTheory_lev_offDiag_normSq_le
-- name    : GlobalTheory.lev_offDiag_normSq_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:54:51.650545+00:00
-- url     : https://prove2.me/theorems/9153d100-15ef-433f-aa4c-17d654f950e2
-- title:
--   Global Theory: lev off Diag norm Sq le
-- statement:
--   The Global Theory construction uses the lev off Diag norm Sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UnitaryGlModuleLevelOffDiagNormSqLe.lean#L148-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UnitaryGlModuleLevelOffDiagNormSqLe.lean#L148-L256

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WeightNearDiagonalOperatorsBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitaryGlModuleLevelOffDiagNormSqLe
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
open Finset
open scoped InnerProductSpace

theorem GlobalTheory.lev_offDiag_normSq_le : ∀ (M : Type) [NormedAddCommGroup M]
    [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M)
    (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), _root_.BranchingSupport.IsMod ε E μ →
    _root_.BranchingSupport.Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 →
    _root_.BranchingSupport.Lev ε E μ j w →
    (n : ℝ) * ∑ a, ∑ b ∈ univ.erase a, ‖E a b w‖ ^ 2 ≤ (bv / 16) ^ 2 * ‖w‖ ^ 2 := by sorry
