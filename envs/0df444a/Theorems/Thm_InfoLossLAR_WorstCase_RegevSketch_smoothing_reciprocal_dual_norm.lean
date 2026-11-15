-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_smoothing_reciprocal_dual_norm
-- name    : InfoLossLAR.WorstCase.RegevSketch.smoothing_reciprocal_dual_norm
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T01:55:54.815923+00:00
-- url     : https://prove2.me/theorems/6dd4eb8f-edd4-410e-8652-9f875054c5f2
-- title:
--   Any true nonzero dual lattice vector lower-bounds the smoothing parameter
-- statement:
--   For a full-rank discrete Euclidean lattice L in positive dimension, every positive error epsilon ≤ exp(-pi), and every actual nonzero point y in its dual lattice, one has 1/||y|| ≤ eta_epsilon(L). This uses the actual full-dual Gaussian smoothing definition and an individual genuine dual term. It supports the existing Gram–Schmidt/BDD stopping analysis without introducing the basis encoding length into its geometric threshold. It supplies no LLL polynomial-time certificate or successful BDD algorithm.
-- source:
--   Complete existing checked proofs from Solutions/RegevBridgeSmoothingLowerBound.lean (smoothing_reciprocal_dual_norm), RegevBridgeSmoothingDualSeparation.lean (smoothing_dual_separation), and the three needed helper proofs dual_mass_le_of_smoothing, rho_width_mono, summable_dual_of_smoothing in RegevBridgeGaussianProjectionSmoothing.lean. Official Lean syntax/info-tree oracle preserves exact source command slices. Only the final required global solution is added. No new mathematical argument.

import Theorems.Thm_RegevLWE_GaussConv_smoothing_remark

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.RegevSketch
open RegevLWE.GaussConv

theorem smoothing_reciprocal_dual_norm {dimension : ℕ}
    (lattice : Submodule ℤ (EuclideanSpace ℝ (Fin dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (error : ℝ) (hdimension : 0 < dimension) (herror : 0 < error) (hsmall : error ≤ Real.exp (-Real.pi))
    (point : dual lattice) (hpoint : point ≠ 0) :
    1/‖(point : EuclideanSpace ℝ (Fin dimension))‖ ≤ smoothingParam lattice error := by sorry

end InfoLossLAR.WorstCase.RegevSketch
