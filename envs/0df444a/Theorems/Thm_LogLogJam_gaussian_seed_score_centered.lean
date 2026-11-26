-- Prove2me | Theorems.Thm_LogLogJam_gaussian_seed_score_centered
-- name    : LogLogJam.gaussian_seed_score_centered
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T09:42:14.154252+00:00
-- url     : https://prove2.me/theorems/2126f175-b2de-4359-889b-e5a65b33f5e7
-- title:
--   Integrability and centering of the Gaussian outcome density derivative
-- statement:
--   Fix a squeezing parameter λ > 1, a physical k-copy Gaussian measurement seed W, and a real angle θ. At each outcome y, its conditional density q(t,y) is differentiable in t at θ. Its parameter derivative is absolutely integrable over outcomes, and its signed integral against Lebesgue measure equals zero. Equivalently, the score has zero conditional mean under the outcome law. The statement also covers a zero-copy seed.
-- source:
--   Chen, Gong, Ye and Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983v1, Section 5, proof of Lemma 5.6 (the conditional score has zero expectation) and its Gaussian application in Corollary 5.7; Section 6, proof of Lemma 6.1 for the Gaussian outcome score. https://arxiv.org/html/2607.12983v1

import Definitions.Def_LogLogJam_Obs
open MeasureTheory Matrix

namespace LogLogJam

theorem gaussian_seed_score_centered (lam θ : ℝ) (hlam : 1 < lam) (k : ℕ) (W : Q k → Q k → ℝ)
    (hW : IsCov k (Matrix.of W)) :
    let q := fun t y => outDens k (VsqK lam t k + Matrix.of W) y
    (∀ y, DifferentiableAt ℝ (fun t => q t y) θ) ∧
    Integrable (fun y => deriv (fun t => q t y) θ) ∧
      (∫ y, deriv (fun t => q t y) θ) = 0 := by sorry

end LogLogJam
