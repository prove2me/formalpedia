-- Prove2me | Theorems.Thm_GlobalTheory_T_tube_chain_holds
-- name    : GlobalTheory.T.tube_chain_holds
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:42:04.997179+00:00
-- url     : https://prove2.me/theorems/2b263a1f-9790-4ea2-b904-bdff3abc4439
-- title:
--   T: tube chain holds
-- statement:
--   The T construction uses the tube chain holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TubeChainHoldsStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TubeChainHoldsStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TubeChainHolds
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TubeChainHoldsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.tube_chain_holds : PositivityTheory.RgEis.TubeChain := by sorry
