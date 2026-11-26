-- Prove2me | Theorems.Thm_LogLogJam_gaussian_seed_mass_one
-- name    : LogLogJam.gaussian_seed_mass_one
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T09:24:46.266399+00:00
-- url     : https://prove2.me/theorems/b49821af-0e20-51a8-9877-d123ead25585
-- title:
--   Normalization of the Gaussian measurement outcome density
-- statement:
--   For $\lambda>1$, $\theta\in\mathbb R$, $k\ge0$ and any real symmetric seed covariance $W$ satisfying $W+i\Omega_k\succeq0$, set $D=V_\theta\otimes I_k+W$, where $V_\theta=R_\theta\operatorname{diag}(\lambda,\lambda^{-1})R_\theta^T$. The density $\exp(-y^TD^{-1}y)/(\pi^k\sqrt{\det D})$ integrates to one with respect to Lebesgue measure on $\mathbb R^{2k}$, including its zero-dimensional instance.
-- source:
--   Normalization of the explicit Gaussian outcome model in Chen, Gong, Ye and Zhang, The loglog jam in Gaussian state tomography, arXiv:2607.12983v1, Section 6.1, Eq. (68). https://arxiv.org/html/2607.12983v1#S6.E68

import Definitions.Def_LogLogJam_IsCov
open MeasureTheory

namespace LogLogJam
theorem gaussian_seed_mass_one (lam θ : ℝ) (hlam : 1 < lam) (k : ℕ) (W : Q k → Q k → ℝ)
    (hW : IsCov k (Matrix.of W)) :
    ∫⁻ y, ENNReal.ofReal (outDens k (VsqK lam θ k + Matrix.of W) y) = 1 := by sorry
end LogLogJam
