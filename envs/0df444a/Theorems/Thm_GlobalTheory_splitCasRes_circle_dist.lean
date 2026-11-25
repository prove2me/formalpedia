-- Prove2me | Theorems.Thm_GlobalTheory_splitCasRes_circle_dist
-- name    : GlobalTheory.splitCasRes_circle_dist
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:54:49.694898+00:00
-- url     : https://prove2.me/theorems/206c1f01-2db0-4e55-99e5-4001fcff30b6
-- title:
--   Global Theory: split Cas Res circle dist
-- statement:
--   The Global Theory construction uses the split Cas Res circle dist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SplitCasimirResolventCircleBounds.lean#L27-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SplitCasimirResolventCircleBounds.lean#L27-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CardFilterFinBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WeightNearDiagonalOperatorsBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasimirOffDiagonalNormSqLeOfLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasimirResolventCircleBounds
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

theorem GlobalTheory.splitCasRes_circle_dist (b t : ℝ) (ζ : ℂ) (hζ : ‖ζ + ((b / 16 : ℝ) : ℂ)‖ = 9 * b / 16)
    (ht : (-b / 8 - b / 32 ≤ -t ∧ -t ≤ b / 32) ∨ b - b / 32 ≤ -t) :
    15 * b / 32 ≤ ‖ζ + (t : ℂ)‖ := by sorry
