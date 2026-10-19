-- Prove2me | Theorems.Thm_OTCChain_Equilibrium_step_III
-- name    : OTCChain.Equilibrium.step_III
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:04.657304+00:00
-- url     : https://prove2.me/theorems/9861b5ee-2fab-4b9c-82b9-5f00bbca2884
-- title:
--   (85)–(87), proof of Theorem 1, Step III, pp. 41–42 (PDF 44–45) — the closed-form values solve the Bellman system and make the cutoff rules optimal
-- statement:
--   Let the standing assumptions hold, $0 < c < c^*$, and let $\Delta_b, \Delta_s \in [0,\bar\Delta]$ solve (20) and (21). Take the candidate densities (55)–(63) (with the corrected (59)–(60)) and the candidate value functions: $V_h(\Delta) = V_h(\Delta_s) + \frac{\Delta - \Delta_s}{\kappa + r}$, $V_n$ the constant (79), $V_s = V(1,\cdot)$ of (82) on $[0,\Delta_s]$ and $V_b = V(0,\cdot)$ of (80) on $[\Delta_b,\bar\Delta]$, with $V_s$ on $(\Delta_s,\bar\Delta]$ and $V_b$ on $[0,\Delta_b)$ given by the right-hand sides of (9) and (11). Then
--
--   1. these value functions solve the Bellman system (8)–(11) for the candidate densities, and
--   2. the decision rules (3)–(4) with cutoffs $\Delta_b$, $\Delta_s$ are optimal under them: $V_b \le V_n$ on $[0,\Delta_b)$, $V_n \le V_b$ on $(\Delta_b,\bar\Delta]$, $V_h \le V_s$ on $[0,\Delta_s)$ and $V_s \le V_h$ on $(\Delta_s,\bar\Delta]$.
--
--   With the existence half of Step I this gives the existence of an intermediation equilibrium. The paper proves optimality by a one-period deviation argument for one of the four cases ((85)–(87)) and states that the others are similar.
-- source:
--   Shen, Wei & Yan, Financial Intermediation Chains in an OTC Market, MPRA Paper No. 74925 (version of October 29, 2016), pp. 41–42 (PDF 44–45), proof of Theorem 1, Step III, (85)–(87)

import Mathlib
import Definitions.Def_OTCChain_Equilibrium_Model
import Definitions.Def_OTCChain_Equilibrium_ClosedForm

namespace OTCChain.Equilibrium

open Set

/-- (85)–(87), proof of Theorem 1, Step III, pp. 41–42: for `0 < c < c*` and the solutions
`∆b`, `∆s ∈ [0, ∆̄]` of (20) and (21), the candidate value functions (79)–(82) (completed off
their pieces by (9) and (11)) solve the Bellman system (8)–(11) for the candidate densities,
and the decision rules (3)–(4) with cutoffs `∆b`, `∆s` are optimal under them. -/
theorem step_III (M : Params) (hM : M.Standing) (hc : 0 < M.c) (hcs : M.c < cStar M)
    (Δb Δs : ℝ) (hb : Δb ∈ Icc 0 M.Δbar) (hb20 : rhs20 M Δb = M.c)
    (hs : Δs ∈ Icc 0 M.Δbar) (hs21 : rhs21 M Δs = M.c) :
    IsBellman M (candDensities M Δb Δs) (candValues M Δb Δs) ∧
      IsOptimal M Δb Δs (candValues M Δb Δs) := by sorry

end OTCChain.Equilibrium
