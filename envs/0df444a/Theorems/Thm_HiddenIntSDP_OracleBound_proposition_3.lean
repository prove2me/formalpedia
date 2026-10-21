-- Prove2me | Theorems.Thm_HiddenIntSDP_OracleBound_proposition_3
-- name    : HiddenIntSDP.OracleBound.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:05:54.695258+00:00
-- url     : https://prove2.me/theorems/4b441cfb-0abb-498e-9734-47b9d3afb92c
-- title:
--   Proposition 3, p. 18 — signal term and separation
-- statement:
--   For every feasible SDP matrix $Y$, write $\gamma=\|Y-Y^*\|_1$, $C_a^*=\{i:\sigma^*(i)=a\}$, $\Delta_{ab}=\|\mu_a-\mu_b\|_2$, and $\Delta=\min_{a\ne b}\Delta_{ab}$. Then
--
--   $$
--   S_4=-\frac12\sum_{a\ne b}\Delta_{ab}^2
--             \sum_{i\in C_a^*,\,j\in C_b^*}(Y-Y^*)_{ij},
--   \qquad
--   S_4\le-\frac14\Delta^2\gamma.
--   $$
--
--   The proposition supplies the negative signal term used to absorb the stochastic error terms.
-- source:
--   Fei & Chen, Hidden integrality and semi-random robustness of SDP relaxation for sub-Gaussian mixture model, arXiv:1803.06510v2, p. 18, Proposition 3

import Definitions.Def_HiddenIntSDP_OracleBound_Proof

namespace HiddenIntSDP.OracleBound

/-- Fei–Chen, Proposition 3, p. 18. -/
theorem proposition_3 {n k d : ℕ} (hn : 4 ≤ n) (hk : 2 ≤ k)
    (mu : Fin k → EuclideanSpace ℝ (Fin d)) (sig : Fin n → Fin k)
    (hbal : Balanced n k sig) (Y : Matrix (Fin n) (Fin n) ℝ)
    (hY : SDPFeasible n k Y) :
    S4 mu sig Y = -(1 / 2 : ℝ) *
      (∑ a, ∑ b ∈ Finset.univ.filter (fun b => b ≠ a),
        ‖mu a - mu b‖ ^ 2 *
          (∑ i ∈ Finset.univ.filter (fun i => sig i = a),
            ∑ j ∈ Finset.univ.filter (fun j => sig j = b),
              (Y - Ystar sig) i j)) ∧
    S4 mu sig Y ≤ -(1 / 4 : ℝ) * minSep mu ^ 2 * gamma sig Y := by sorry

end HiddenIntSDP.OracleBound
