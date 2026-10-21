-- Prove2me | Theorems.Thm_LNChannels_Exact_theorem_1_i_min
-- name    : LNChannels.Exact.theorem_1_i_min
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:59.225351+00:00
-- url     : https://prove2.me/theorems/208cb07b-a5ca-48dc-bbc0-ef8706ef9550
-- title:
--   Theorem 1 (i), (2), p. 6 — the minimal cost of a unidirectional channel
-- statement:
--   Let $B>0$, $\lambda_2>0$, $r>0$ and set $k=B\log(1+r/\lambda_2)$. Over real channel sizes $m>0$, the unidirectional cost $m+B\big(((r+\lambda_2)/\lambda_2)^m-1\big)^{-1}$ of (1) has the minimum value
--
--   $$c^{opt}(0,\lambda_2)=\frac{B}{2k}\left(-k+\sqrt{k(k+4)}+2\log\Big(\tfrac12\big(k+\sqrt{k(k+4)}+2\big)\Big)\right),$$
--
--   and the minimum is attained at
--
--   $$l_2=\frac{B}{k}\log\Big(\tfrac12\big(k+\sqrt{k(k+4)}+2\big)\Big)>0.$$
--
--   This gives the optimal size and cost of a unidirectional channel in closed form.
--
--   **Formalization Note** The minimization is over real sizes $m>0$ (the paper differentiates in $l_2$), with the real power `Real.rpow`. The paper writes $c^{opt}(0,\lambda)$ with $k$ defined from $\lambda_2$; here $\lambda=\lambda_2$. $B>0$ is required: for $B=0$ the infimum $0$ is not attained.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 6 (PDF p. 7), Theorem 1 (i), equation (2); proof §5.2, pp. 10–11

import Mathlib
import Definitions.Def_LNChannels_Exact_uniCost

set_option autoImplicit false

namespace LNChannels.Exact

/-- Theorem 1 (i), (2), p. 6: with `k = B log(1 + r/λ₂)`, the minimum over real sizes `m > 0` of
the unidirectional cost (1) is `(B/(2k))(−k + √(k(k+4)) + 2 log(½(k + √(k(k+4)) + 2)))`, attained at
`l₂ = (B/k) log(½(k + √(k(k+4)) + 2))`. -/
theorem theorem_1_i_min (lam₂ r B : ℝ) (hB : 0 < B) (hlam₂ : 0 < lam₂) (hr : 0 < r) :
    let k := B * Real.log (1 + r / lam₂)
    let copt := B / (2 * k) * (-k + Real.sqrt (k * (k + 4))
      + 2 * Real.log ((1 / 2) * (k + Real.sqrt (k * (k + 4)) + 2)))
    let lstar := B / k * Real.log ((1 / 2) * (k + Real.sqrt (k * (k + 4)) + 2))
    IsLeast (uniCost lam₂ r B '' Set.Ioi 0) copt ∧ 0 < lstar ∧
      uniCost lam₂ r B lstar = copt := by sorry

end LNChannels.Exact
