-- Prove2me | Theorems.Thm_GlobalTheory_T_smooth_spreads_out
-- name    : GlobalTheory.T.smooth_spreads_out
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:38:12.990157+00:00
-- url     : https://prove2.me/theorems/b8d7f2aa-4265-4fbe-85d5-60cb6b2838ce
-- title:
--   T: smooth spreads out
-- statement:
--   The T construction uses the smooth spreads out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SmoothSpreadsOutStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SmoothSpreadsOutStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SmoothSpreadsOut
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SmoothSpreadsOutStatement
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

theorem GlobalTheory.T.smooth_spreads_out : GlobalTheory.SpreadingModels.Spreads (fun _ _ f => Smooth f) := by sorry
