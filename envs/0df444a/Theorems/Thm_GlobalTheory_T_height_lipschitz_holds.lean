-- Prove2me | Theorems.Thm_GlobalTheory_T_height_lipschitz_holds
-- name    : GlobalTheory.T.height_lipschitz_holds
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:32:45.1432+00:00
-- url     : https://prove2.me/theorems/cf6d650c-7c0e-4cac-b881-fbad435dd2f3
-- title:
--   T: height lipschitz holds
-- statement:
--   The T construction uses the height lipschitz holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HeightLipschitzHoldsStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HeightLipschitzHoldsStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HeightLipschitzHolds
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HeightLipschitzHoldsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.height_lipschitz_holds : PositivityTheory.RgEis.HtLip := by sorry
