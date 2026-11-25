-- Prove2me | Theorems.Thm_GlobalTheory_T_isProper_spreads_out
-- name    : GlobalTheory.T.isProper_spreads_out
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:35:50.620476+00:00
-- url     : https://prove2.me/theorems/68fe4d91-25f6-5f3f-8fe6-39fc7ec09cb7
-- title:
--   T: is Proper spreads out
-- statement:
--   The T construction uses the is Proper spreads out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOutStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOutStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsProperSpreadsOut
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsProperSpreadsOutStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GlobalTheory.SpreadingModels
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isProper_spreads_out : GlobalTheory.SpreadingModels.Spreads (fun _ _ f => IsProper f) := by sorry
