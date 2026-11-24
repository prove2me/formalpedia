-- Prove2me | Theorems.Thm_GlobalTheory_T_pattern_set_card_column_step
-- name    : GlobalTheory.T.pattern_set_card_column_step
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:55:05.707623+00:00
-- url     : https://prove2.me/theorems/a650c7c7-790d-4288-a2de-bb43ade01b97
-- title:
--   T: pattern set card column step
-- statement:
--   The T construction uses the pattern set card column step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PatternSetCardColumnStepStatement.lean#L8-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PatternSetCardColumnStepStatement.lean#L8-L10

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternSetCardColumnStep
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternSetCardColumnStepStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.pattern_set_card_column_step : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ), j < d →
    (patSet K (colGe d j)).ncard = Fintype.card K ^ j * (patSet K (colGe d (j + 1))).ncard := by sorry
