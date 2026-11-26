-- Prove2me | Theorems.Thm_LogLogJam_seed_fisher_pointwise
-- name    : LogLogJam.seed_fisher_pointwise
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T09:24:49.620292+00:00
-- url     : https://prove2.me/theorems/32745e4c-2164-49e7-9b72-0ddf3d3d5b50
-- title:
--   Pointwise Fisher information of a Gaussian batch measurement
-- statement:
--   For every squeezing parameter $\lambda>1$, angle $\theta\in\mathbb R$, batch size $k\ge0$, and real symmetric $2k$-dimensional seed covariance $W$ satisfying $W+i\Omega_k\succeq0$, the angle Fisher information in a single measurement of the $k$-copy batch is at most $16kE^2$, where $E=(\lambda+\lambda^{-1})/4$. The outcome is the centered real Gaussian with covariance $(V_\theta\otimes I_k+W)/2$ and $V_\theta=R_\theta\operatorname{diag}(\lambda,\lambda^{-1})R_\theta^T$. The bound holds at each angle.
-- source:
--   Auxiliary consequence formulated for the rotated squeezed states and adaptive observation model in Chen, Gong, Ye and Zhang, The loglog jam in Gaussian state tomography, arXiv:2607.12983v1. Section 6.1, Eqs. (68)–(69), gives the outcome density and angular Fisher information. The pointwise estimate follows by adding independent Gaussian seed noise to the noiseless rotated samples and applying classical Fisher data processing. https://arxiv.org/html/2607.12983v1#S6.E68

import Definitions.Def_LogLogJam_Obs

open scoped ENNReal

namespace LogLogJam

theorem seed_fisher_pointwise (lam θ : ℝ) (hlam : 1 < lam) (k : ℕ)
    (W : Q k → Q k → ℝ) (hW : IsCov k (Matrix.of W)) :
    measFisher lam k W θ ≤ ENNReal.ofReal ((4 * energy lam)^2) * (k : ℝ≥0∞) := by sorry

end LogLogJam
