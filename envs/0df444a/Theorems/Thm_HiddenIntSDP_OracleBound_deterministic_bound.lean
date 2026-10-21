-- Prove2me | Theorems.Thm_HiddenIntSDP_OracleBound_deterministic_bound
-- name    : HiddenIntSDP.OracleBound.deterministic_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:05:47.078995+00:00
-- url     : https://prove2.me/theorems/b42c3cae-222d-49da-9a94-3af5efc55ceb
-- title:
--   Final display, p. 20 — deterministic SDP-to-Oracle bound
-- statement:
--   Fix a balanced mixture realization and a feasible SDP matrix $Y$ for which the deterministic inequality $0\le S_3+\tfrac14 S_4$ holds. With $\gamma=\|Y-Y^*\|_1$ and $\ell=n/k$, the paper obtains
--   $$
--   \gamma\le4\ell\,IP_1
--          =2\ell\max\{\|F-F^*\|_1:F\in\mathcal F,\ \eta(F)\le\eta(F^*)\}.
--   $$
--   The second equality is expressed through Lemma 2's identity between $IP_1$ and the half-$\ell_1$ Oracle error. This bound is the deterministic part of Theorem 1.
--
--   **Formalization Note** Zero SDP error is included; the proof discussion temporarily assumes $\gamma>0$, but the displayed conclusion holds at $\gamma=0$.
-- source:
--   Fei & Chen, Hidden integrality and semi-random robustness of SDP relaxation for sub-Gaussian mixture model, arXiv:1803.06510v2, p. 20, final display after Lemma 2; p. 18, (17)

import Definitions.Def_HiddenIntSDP_OracleBound_Proof

namespace HiddenIntSDP.OracleBound

/-- Fei–Chen, final display of p. 20, under inequality (17). -/
theorem deterministic_bound {n k d : ℕ} (hn : 4 ≤ n) (hk : 2 ≤ k)
    (mu : Fin k → EuclideanSpace ℝ (Fin d)) (sig : Fin n → Fin k)
    (hbal : Balanced n k sig) (g : Fin n → EuclideanSpace ℝ (Fin d))
    (Y : Matrix (Fin n) (Fin n) ℝ) (hY : SDPFeasible n k Y)
    (h17 : 0 ≤ S3 mu sig g Y + (1 / 4 : ℝ) * S4 mu sig Y) :
    gamma sig Y ≤ 4 * ell n k * IP1 mu sig g ∧
    IP1 mu sig g = oracleErr mu sig g := by sorry

end HiddenIntSDP.OracleBound
