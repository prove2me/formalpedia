-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_smoothing_le_short_independent
-- name    : InfoLossLAR.WorstCase.RegevSketch.smoothing_le_short_independent
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T01:42:10.925514+00:00
-- url     : https://prove2.me/theorems/0749ecc1-4494-45c6-b0e4-68690e4f1ba5
-- title:
--   A true short independent lattice family gives logarithmic smoothing
-- statement:
--   Let L be a real Euclidean lattice of dimension n>0, with full-rank discrete dual. Suppose L contains n real-linearly-independent vectors, each of norm at most a positive radius r. For every error epsilon>0, its actual smoothing parameter satisfies eta_epsilon(L) ≤ r sqrt(log(4 n (1+1/epsilon))/pi). The vectors are mathematical witnesses; the theorem neither assumes nor produces an efficient short-basis algorithm. The smoothing parameter and Gaussian use the existing GaussConv pi/width convention.
-- source:
--   Complete existing checked proof InfoLossLAR.WorstCase.GaussianPoissonSeries.smoothing_le_short_independent in Solutions/RegevBridgeSharpSmoothingFamily.lean, together with its minimal mathematical proof closure. Official Lean declaration and syntax/info-tree oracles select source slices; the public statement only delta-expands shortSmoothingFactor and the Euclidean Space alias. No new mathematical argument. This sharp smoothing prerequisite supports Regev 3.3→3.1 and 3.15–3.17; it is not itself a complete DGS/SIVP/GapSVP reduction.

import Mathlib
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Theorems.Thm_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq
import Theorems.Thm_SchwartzMap_tsum_eq_tsum_fourier_euclideanSpace
import Theorems.Thm_ZLattice_tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral
import Theorems.Thm_RegevLWE_GaussConv_fourier_rhoShift
import Theorems.Thm_ZLattice_summable_fourierIntegral_mul_fourierChar_dualSubmodule

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.RegevSketch
open RegevLWE.GaussConv

theorem smoothing_le_short_independent {dimension : ℕ}
    (lattice : Submodule ℤ (EuclideanSpace ℝ (Fin dimension)))
    [DiscreteTopology (dual lattice)] [IsZLattice ℝ (dual lattice)]
    (directions : Fin dimension → lattice)
    (hindependent : LinearIndependent ℝ (fun index => (directions index : EuclideanSpace ℝ (Fin dimension))))
    (radius error : ℝ) (hdimension : 0 < dimension) (hradius : 0 < radius) (herror : 0 < error)
    (hbound : ∀ index,‖(directions index : EuclideanSpace ℝ (Fin dimension))‖ ≤ radius) :
    smoothingParam lattice error ≤
      Real.sqrt (Real.log (4*(dimension : ℝ)*(1+1/error))/Real.pi)*radius := by sorry

end InfoLossLAR.WorstCase.RegevSketch
