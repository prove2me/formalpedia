-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_smoothingError_log_factor
-- name    : InfoLossLAR.WorstCase.RegevSketch.smoothingError_log_factor
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T01:34:12.063195+00:00
-- url     : https://prove2.me/theorems/1afbdab1-db40-4590-9080-cbf46001b08a
-- title:
--   The fixed negligible smoothing schedule has an absolute logarithmic cost
-- statement:
--   At every positive dimension n, the same fixed schedule epsilon(n)=2^(-(Nat.size(n+2))^2) used in the DGS sketch satisfies sqrt(log(4 n (1+1/epsilon(n)))/pi) ≤ (4/log 2) log(n+2). The logarithmic factor has an absolute constant independent of the adversary, sample exponent and basis encoding length. This is the explicit numerical smoothing-factor estimate; it does not itself assert a lattice smoothing bound or construct a lattice algorithm.
-- source:
--   Complete existing checked proofs from Solutions/RegevBridgeNegligibleSmoothingError.lean: fixedSmoothingError_pos, fixedSmoothingFactor_le_size, dimension_size_le_log and fixedSmoothingFactor_le_log. The function fixedSmoothingError is definitionally equal to the already published RegevSketch.smoothingError. shortSmoothingFactor is expanded only in the public statement. No new mathematical argument is introduced.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.RegevSketch

theorem smoothingError_log_factor (dimension : ℕ) (hdimension : 0 < dimension) :
    Real.sqrt (Real.log (4*(dimension : ℝ)*(1+1/smoothingError dimension))/Real.pi) ≤
      (4/Real.log 2)*Real.log (dimension+2) := by sorry

end InfoLossLAR.WorstCase.RegevSketch
