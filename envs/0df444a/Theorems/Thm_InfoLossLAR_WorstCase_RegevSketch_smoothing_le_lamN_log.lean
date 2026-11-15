-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_smoothing_le_lamN_log
-- name    : InfoLossLAR.WorstCase.RegevSketch.smoothing_le_lamN_log
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T01:50:48.853447+00:00
-- url     : https://prove2.me/theorems/8f2255b5-42b9-4dc7-b957-66cbe832ccd0
-- title:
--   Sharp smoothing for the literal last successive minimum at the fixed negligible schedule
-- statement:
--   For every positive dimension n and nonsingular integer input basis B, the actual Gaussian smoothing parameter of its lattice at the same fixed negligible schedule epsilon(n) used in the DGS sketch is at most (4/log 2) log(n+2) times the literal target-defined last successive minimum lambda_n(B). The constant is absolute and independent of the adversary, sample exponent and basis encoding length. The proof uses the infimum definition directly, without assuming that a short independent family is efficiently found. This is a smoothing bound, not an algorithmic DGS/SIVP/GapSVP reduction.
-- source:
--   Complete existing checked proof GaussianPoissonSeries.smoothing_fixed_negligible_le_lamN_log and its original-basis/last-minimum helper proofs, extracted by official Lean syntax/info-tree oracle from Solutions/RegevBridgeFixedLogSmoothing.lean, RegevBridgeSharpSmoothingLastMinimum.lean, RegevBridgeIntegerBasis.lean, RegevBridgeIntegerDualCoordinates.lean, RegevBridgeSharpSmoothingParameters.lean, RegevBridgeNegligibleSmoothingError.lean and RegevBridgeLatticeInterfaces.lean. The already checked generic smoothing and logarithmic factor are reused through their formal APIs. Renaming is semantically checked by Lean definitional equality. No new mathematical argument.

import Definitions.Def_InfoLossLAR_IntegerBasis_Core
import Definitions.Def_InfoLossLAR_RegevSketch_DGS
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_smoothing_le_short_independent
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_smoothingError_log_factor

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.RegevSketch

theorem smoothing_le_lamN_log {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (hdimension : 0 < dimension) :
    RegevLWE.GaussConv.smoothingParam (IntegerBasis.inputLattice basis hdet) (smoothingError dimension) ≤
      (4/Real.log 2)*Real.log (dimension+2)*InfoLossLAR.WorstCase.lamN basis := by sorry

end InfoLossLAR.WorstCase.RegevSketch
