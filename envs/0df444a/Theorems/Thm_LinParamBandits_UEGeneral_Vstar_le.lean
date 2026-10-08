-- Prove2me | Theorems.Thm_LinParamBandits_UEGeneral_Vstar_le
-- name    : LinParamBandits.UEGeneral.Vstar_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:59.274177+00:00
-- url     : https://prove2.me/theorems/5918696a-7d18-46a1-adf2-2a698bcf8970
-- title:
--   Lemma B.11 — V*(c, t) ≤ 2c₀(r log c₀ + (r+1) log(r+t+1))
-- statement:
--   Let $r \ge 2$. For all $c \ge 0$ and all integers $t \ge 1$,
--   $$V^*(c, t) \le 2c_0\big(r\log c_0 + (r+1)\log(r+t+1)\big), \qquad c_0 = \max\{1, c\},$$
--   where $V^*(c, t)$ is the value of the optimization problem on p. 38 in dimension $r$.
--
--   This is the deterministic estimate that turns Lemma B.10 into the $\log T$ growth of $\sum_t \|U_{t+1}\|^2_{C_t}$, and hence the $\sqrt T\log^{3/2}T$ term of Theorem 4.1.
--
--   **Formalization Note** $c_0 = \max\{1, c\}$ is written `max 1 c`; it is a different quantity from the $c_0 = \bar u^2/\lambda_0$ of the proof of Lemma B.10. The standing assumption $r \ge 2$ of the paper is a hypothesis (the proof uses $e/(r+1) \le 1$).
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Lemma B.11, p. 38 (proof p. 39)

import Mathlib
import Definitions.Def_LinParamBandits_UEGeneral_Vstar

namespace LinParamBandits.UEGeneral

/-- Lemma B.11 (p. 38): optimization bound, with `c₀ = max{1, c}` written `max 1 c`. -/
theorem Vstar_le {r : ℕ} (hr : 2 ≤ r) (c : ℝ) (hc : 0 ≤ c) (t : ℕ) (ht : 1 ≤ t) :
    Vstar r c t ≤
      2 * max 1 c * ((r : ℝ) * Real.log (max 1 c) + ((r : ℝ) + 1) * Real.log ((r : ℝ) + t + 1)) := by sorry

end LinParamBandits.UEGeneral
