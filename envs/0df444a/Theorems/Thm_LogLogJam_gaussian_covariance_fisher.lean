-- Prove2me | Theorems.Thm_LogLogJam_gaussian_covariance_fisher
-- name    : LogLogJam.gaussian_covariance_fisher
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T09:31:19.601292+00:00
-- url     : https://prove2.me/theorems/6774191d-7687-4d05-82e2-5dabf366fedc
-- title:
--   Fisher information of a centered Gaussian covariance curve
-- statement:
--   Let $k\ge0$ and let $D(t)$ be a positive-definite real $2k\times2k$ matrix for every real $t$. Fix $\theta\in\mathbb R$ at which every entry has a derivative, and write $H_{ij}=D_{ij}'(\theta)$. For the centered Gaussian density $f_t(y)=\exp(-y^TD(t)^{-1}y)/(\pi^k\sqrt{\det D(t)})$, the Fisher information in the parameter at $\theta$ equals $\frac12\operatorname{tr}(D(\theta)^{-1}H D(\theta)^{-1}H)$. The integral defining Fisher information uses Lebesgue measure on $\mathbb R^{2k}$ and the squared logarithmic derivative. The real trace expression is embedded into the extended nonnegative reals by taking its positive part.
-- source:
--   Chen, Gong, Ye and Zhang, The loglog jam in Gaussian state tomography, arXiv:2607.12983v1, Section 6.1, proof of Lemma 6.1 immediately following Eq. (70), displayed centered-Gaussian Fisher information identities. Formulated for a general positive-definite covariance curve with entrywise derivative at the parameter of interest. https://arxiv.org/html/2607.12983v1#S6.Thmtheorem1

import Definitions.Def_LogLogJam_Obs
open MeasureTheory Matrix
open scoped ENNReal

namespace LogLogJam
theorem gaussian_covariance_fisher (k : ℕ) (D : ℝ → Matrix (Q k) (Q k) ℝ)
    (H : Matrix (Q k) (Q k) ℝ) (θ : ℝ) (hD : ∀ t, (D t).PosDef)
    (hd : ∀ i j, HasDerivAt (fun t => D t i j) (H i j) θ) :
    fisherInfo volume (fun t y => outDens k (D t) y) θ =
      ENNReal.ofReal (((((D θ)⁻¹ * H) * ((D θ)⁻¹ * H)).trace) / 2) := by sorry
end LogLogJam
