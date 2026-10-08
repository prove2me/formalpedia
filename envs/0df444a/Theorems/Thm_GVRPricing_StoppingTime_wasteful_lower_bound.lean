-- Prove2me | Theorems.Thm_GVRPricing_StoppingTime_wasteful_lower_bound
-- name    : GVRPricing.StoppingTime.wasteful_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:06:11.295029+00:00
-- url     : https://prove2.me/theorems/7e7daf31-dd99-406b-8b0e-bb68fffeea6a
-- title:
--   Proof of Theorem 5 — $J^W(n,t')\ge p_k[m-\frac12\sqrt m]+p_{k+1}[(n-m)-\frac12\sqrt{n-m}]$ and the ratio bound
-- statement:
--   Let $1\le k\le K-1$, $n\in\mathbb N$ and $t$ satisfy $\lambda_k t\ge n>\lambda_{k+1}t$, let $m=\lceil\lambda_k t_k\rceil$ and let $t'$ be the shrunk horizon of (28), at which $\lambda_k t_m=m$ and $\lambda_{k+1}(t'-t_m)=n-m$. Then
--
--   1. $$J^W(n,t')\ge p_k\Big[m-\tfrac12\sqrt m\Big]+p_{k+1}\Big[(n-m)-\tfrac12\sqrt{n-m}\Big];$$
--   2. $J^D(n,t')=p_k m+p_{k+1}(n-m)$;
--   3. if $m<n$, $$\frac{J^W(n,t')}{J^D(n,t')}\ge 1-\frac12\Big[\frac1{\sqrt m}+\frac1{\sqrt{n-m}}\Big].$$
--
--   Together with (29) this bound yields the asymptotic optimality of the ST heuristic.
--
--   **Formalization Note** The page writes the bound at horizon $t$ after passing to a subsequence on which $m=\alpha\lambda_k t$ and $n-m=\bar\alpha\lambda_{k+1}t$ are integers; here it is stated at the shrunk horizon $t'$, where $\alpha\lambda_k t'=m$ and $\bar\alpha\lambda_{k+1}t'=n-m$ hold exactly, so no subsequence is needed. "$1/2\sqrt{x}$" on the page means $\tfrac12\sqrt x$. The ratio bound needs $m<n$ (the page's $\bar\alpha>0$), since $1/\sqrt{n-m}$ is undefined otherwise; $m\ge1$ always holds in this regime. Lean index `k` is the paper's $k$ minus one.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1018 (PDF 20), Appendix, Proof of Theorem 5, last three displays

import Mathlib
import Definitions.Def_GVRPricing_StoppingTime_DetLP
import Definitions.Def_GVRPricing_StoppingTime_Wasteful

namespace GVRPricing.StoppingTime

/-- Appendix, Proof of Theorem 5 (p. 1018): at the shrunk horizon `t'` (where `λ_k t_m = m` and
`λ_{k+1}(t' − t_m) = n − m`), with `m = ⌈λ_k t_k⌉`,
1. `J^W(n, t') ≥ p_k [m − ½√m] + p_{k+1} [(n − m) − ½√(n − m)]`;
2. `J^D(n, t') = p_k m + p_{k+1}(n − m)`;
3. if `m < n`, `J^W(n, t')/J^D(n, t') ≥ 1 − ½ (1/√m + 1/√(n − m))`.
(0-based `k`, `k + 1 < K`, `λ_{k+1} t < n ≤ λ_k t`.) -/
theorem wasteful_lower_bound {K : ℕ} (M : Menu K) (k : ℕ) (hk : k + 1 < K) (n : ℕ) (t : ℝ)
    (hup : (n : ℝ) ≤ M.lamN k * t) (hlow : M.lamN (k + 1) * t < n) :
    M.pN k * ((stM M k n t : ℝ) - 1 / 2 * Real.sqrt (stM M k n t))
        + M.pN (k + 1) * (((n : ℝ) - stM M k n t) - 1 / 2 * Real.sqrt ((n : ℝ) - stM M k n t))
      ≤ jW M k n (shrunkHorizon M k n t) ∧
    detValue M n (shrunkHorizon M k n t)
      = M.pN k * stM M k n t + M.pN (k + 1) * ((n : ℝ) - stM M k n t) ∧
    (stM M k n t < n →
      1 - 1 / 2 * (1 / Real.sqrt (stM M k n t) + 1 / Real.sqrt ((n : ℝ) - stM M k n t))
        ≤ jW M k n (shrunkHorizon M k n t) / detValue M n (shrunkHorizon M k n t)) := by sorry

end GVRPricing.StoppingTime
