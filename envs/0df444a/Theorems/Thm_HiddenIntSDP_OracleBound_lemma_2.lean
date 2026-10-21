-- Prove2me | Theorems.Thm_HiddenIntSDP_OracleBound_lemma_2
-- name    : HiddenIntSDP.OracleBound.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:04.116037+00:00
-- url     : https://prove2.me/theorems/bfb7f736-009a-4b93-a2b3-0ea0fc71440e
-- title:
--   Lemma 2, p. 20 — IP₁ equals the Oracle IP error
-- statement:
--   For any realized noise vectors in the balanced mixture model, the zero-one program $IP_1$ of (23) equals the worst-case error of an Oracle IP solution:
--   $$
--   IP_1=\max\left\{\frac12\|F-F^*\|_1:
--    F\in\mathcal F,\ \eta(F)\le\eta(F^*)\right\}.
--   $$
--   Here $\mathcal F$ contains all assignments with one center per point, without a balance constraint, and $\eta$ uses the augmented observations $\bar h_j=\mu_{\sigma^*(j)}+4g_j$. The equality identifies the integral LP benchmark with the paper's statistical benchmark.
-- source:
--   Fei & Chen, Hidden integrality and semi-random robustness of SDP relaxation for sub-Gaussian mixture model, arXiv:1803.06510v2, p. 20, Lemma 2; p. 24, (25)

import Definitions.Def_HiddenIntSDP_OracleBound_Proof

namespace HiddenIntSDP.OracleBound

/-- Fei–Chen, Lemma 2, p. 20: the integer program (23) equals the
worst-case Oracle IP error (12). -/
theorem lemma_2 {n k d : ℕ} (hn : 4 ≤ n) (hk : 2 ≤ k)
    (mu : Fin k → EuclideanSpace ℝ (Fin d)) (sig : Fin n → Fin k)
    (hbal : Balanced n k sig) (g : Fin n → EuclideanSpace ℝ (Fin d)) :
    IP1 mu sig g = oracleErr mu sig g := by sorry

end HiddenIntSDP.OracleBound
