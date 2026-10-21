-- Prove2me | Theorems.Thm_OTCChain_Equilibrium_eq_84
-- name    : OTCChain.Equilibrium.eq_84
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:39.845323+00:00
-- url     : https://prove2.me/theorems/0f871f89-20bf-4909-ae5c-480279cb0f10
-- title:
--   (84), proof of Theorem 1, Step II, p. 41 (PDF 44) — c* is well defined, and the cutoffs satisfy Δ_b < Δ_s iff c < c*
-- statement:
--   Let the standing assumptions hold, let $\mathrm{rhs}_{20}$, $\mathrm{rhs}_{21}$ be the right-hand sides of (20), (21) as functions of the cutoff, let $\delta^* = \inf\{\delta \in [0,\bar\Delta] : \mathrm{rhs}_{21}(\delta) \le \mathrm{rhs}_{20}(\delta)\}$ and $c^* = \mathrm{rhs}_{20}(\delta^*)$. Then
--
--   1. $\delta^* \in (0,\bar\Delta)$ and $\mathrm{rhs}_{20}(\delta^*) = \mathrm{rhs}_{21}(\delta^*)$, and $\delta^*$ is the only point of $[0,\bar\Delta]$ where the two curves meet; so $c^*$ is the search cost at which $\Delta_b(c^*) = \Delta_s(c^*)$, as in (84);
--   2. $0 < c^* \le \mathrm{rhs}_{20}(\bar\Delta)$ and $c^* \le \mathrm{rhs}_{21}(0)$;
--   3. for every $c > 0$ and all solutions $\Delta_b, \Delta_s \in [0,\bar\Delta]$ of $\mathrm{rhs}_{20}(\Delta_b) = c$ and $\mathrm{rhs}_{21}(\Delta_s) = c$,
--   $$\Delta_b < \Delta_s \iff c < c^*.$$
--
--   This is the threshold of Theorem 1: an intermediary sector $(\Delta_b,\Delta_s)$ exists exactly for search costs below $c^*$.
-- source:
--   Shen, Wei & Yan, Financial Intermediation Chains in an OTC Market, MPRA Paper No. 74925 (version of October 29, 2016), p. 41 (PDF 44), proof of Theorem 1, Step II, (84)

import Mathlib
import Definitions.Def_OTCChain_Equilibrium_Model
import Definitions.Def_OTCChain_Equilibrium_ClosedForm

namespace OTCChain.Equilibrium

open Set

/-- (84), proof of Theorem 1, Step II, p. 41: `δ* ∈ (0, ∆̄)` is the unique point of `[0, ∆̄]`
where the right-hand sides of (20) and (21) cross, so `c* = rhs20(δ*) = rhs21(δ*)` is the cost
at which `∆b(c*) = ∆s(c*)`; `c*` is positive, both (20) and (21) are solvable for every
`0 < c ≤ c*`, and for every `c > 0` the solutions `∆b`, `∆s` of (20), (21) in `[0, ∆̄]` satisfy
`∆b < ∆s` iff `c < c*`. -/
theorem eq_84 (M : Params) (hM : M.Standing) :
    δStar M ∈ Ioo 0 M.Δbar ∧ rhs20 M (δStar M) = rhs21 M (δStar M) ∧
    (∀ δ ∈ Icc 0 M.Δbar, rhs20 M δ = rhs21 M δ → δ = δStar M) ∧
    0 < cStar M ∧ cStar M ≤ rhs20 M M.Δbar ∧ cStar M ≤ rhs21 M 0 ∧
    ∀ c δb δs : ℝ, 0 < c → δb ∈ Icc 0 M.Δbar → rhs20 M δb = c →
      δs ∈ Icc 0 M.Δbar → rhs21 M δs = c → (δb < δs ↔ c < cStar M) := by sorry

end OTCChain.Equilibrium
