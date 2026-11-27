-- Prove2me | Theorems.Thm_GlobalTheory_T_unipotent_convergence_of_parabolic
-- name    : GlobalTheory.T.unipotent_convergence_of_parabolic
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:40:39.083266+00:00
-- url     : https://prove2.me/theorems/5fe35802-1c65-46de-a141-6d604bd6bce1
-- title:
--   T: unipotent convergence of parabolic
-- statement:
--   The T construction uses the unipotent convergence of parabolic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnipotentConvergenceOfParabolicStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnipotentConvergenceOfParabolicStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnipotentConvergenceOfParabolic
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnipotentConvergenceOfParabolicStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.unipotent_convergence_of_parabolic : PositivityTheory.RgEis.ParLaw → PositivityTheory.RgEis.ConvU := by sorry
