-- Prove2me | Theorems.Thm_LogLogJam_transcript_fisher_copy_cap
-- name    : LogLogJam.transcript_fisher_copy_cap
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T09:18:32.236045+00:00
-- url     : https://prove2.me/theorems/80fa5304-8247-533d-96dc-714a8e7666d5
-- title:
--   A copy bound on the Fisher information of an adaptive squeezing-angle experiment
-- statement:
--   Fix a squeezing parameter $\lambda>1$ and write $E=(\lambda+\lambda^{-1})/4$. Consider any protocol of $T\geq0$ Gaussian measurement rounds on the family with covariance $R_\theta\operatorname{diag}(\lambda,\lambda^{-1})R_\theta^T$. Each round may select its batch size and measurement seed at random, conditionally on the observed history. If the total number of copies is at most $S$ almost surely for each real angle $\theta$, the transcript Fisher information averaged over a uniform angle in $[0,\pi)$ satisfies $\overline J_T\leq16 E^2 S$. The estimator and its accuracy play no role in this inequality.
-- source:
--   Auxiliary bound derived for the rotated squeezing family of Task 5.1 in Chen, Gong, Ye and Zhang, The loglog jam in Gaussian state tomography, arXiv:2607.12983v1. Section 5.4, Corollary 5.7 and Eq. (53) give the conditional Fisher chain rule. Section 6.1, Eqs. (68)–(69), specifies the Gaussian outcome model and its Fisher information. The displayed copy cap is an additional consequence, formulated here. https://arxiv.org/html/2607.12983v1#S6.E68

import Definitions.Def_LogLogJam_GaussProtocol

open scoped ENNReal

namespace LogLogJam

theorem transcript_fisher_copy_cap (lam : ℝ) (hlam : 1 < lam) {T : ℕ}
    (P : GaussProtocol T) (S : ℕ) (hS : CopiesLe lam P S) :
    Jbar lam P T ≤ ENNReal.ofReal ((4 * energy lam)^2 * (S : ℝ)) := by sorry

end LogLogJam
