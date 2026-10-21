-- Prove2me | Theorems.Thm_HiddenIntSDP_OracleBound_basic_inequality_16
-- name    : HiddenIntSDP.OracleBound.basic_inequality_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:05:46.361241+00:00
-- url     : https://prove2.me/theorems/c93671cc-2b7c-4a85-b8df-794ffd0e8370
-- title:
--   Equation (16), p. 18 — basic SDP optimality inequality
-- statement:
--   For a balanced mixture realization, let $Y$ minimize the SDP (7), and let $A$ be the squared-distance matrix of the observed points. The paper's error decomposition gives
--
--   $$
--   0\le-\frac12\langle Y-Y^*,A\rangle
--     = S_1+S_2+2S_3+S_4.
--   $$
--
--   Here $S_1$ and $S_2$ split the noise Gram-matrix term by the projection onto the tangent space of $Y^*$, $S_3$ is the mixed noise-center term, and $S_4$ is the center Gram-matrix term. This is the starting inequality for the comparison.
--
--   **Formalization Note** The displayed identity is the deterministic last line of (16); the intervening expectation terms cancel under the model's zero-mean assumption.
-- source:
--   Fei & Chen, Hidden integrality and semi-random robustness of SDP relaxation for sub-Gaussian mixture model, arXiv:1803.06510v2, p. 18, (16)

import Definitions.Def_HiddenIntSDP_OracleBound_Proof

namespace HiddenIntSDP.OracleBound

/-- Fei–Chen, equation (16), p. 18, after cancellation of the expectation terms. -/
theorem basic_inequality_16 {n k d : ℕ} (hn : 4 ≤ n) (hk : 2 ≤ k)
    (mu : Fin k → EuclideanSpace ℝ (Fin d)) (sig : Fin n → Fin k)
    (hbal : Balanced n k sig) (g : Fin n → EuclideanSpace ℝ (Fin d))
    (Y : Matrix (Fin n) (Fin n) ℝ)
    (hY : IsSDPOpt n k (distMat (fun i => mu (sig i) + g i)) Y) :
    0 ≤ -(1 / 2 : ℝ) * frob (Y - Ystar sig)
      (distMat (fun i => mu (sig i) + g i)) ∧
    -(1 / 2 : ℝ) * frob (Y - Ystar sig)
      (distMat (fun i => mu (sig i) + g i)) =
        S1 sig g Y + S2 sig g Y + 2 * S3 mu sig g Y + S4 mu sig Y := by sorry

end HiddenIntSDP.OracleBound
