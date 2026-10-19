-- Prove2me | Theorems.Thm_OTCChain_Equilibrium_eq_21
-- name    : OTCChain.Equilibrium.eq_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:43.554461+00:00
-- url     : https://prove2.me/theorems/000f13e5-86eb-4c94-9293-1bc1d6b4d228
-- title:
--   (21), proof of Theorem 1, Step II, p. 41 (PDF 44) — the seller-cutoff equation has a unique root, and every equilibrium's Δ_s solves it
-- statement:
--   Let the standing assumptions hold and let
--   $$\mathrm{rhs}_{21}(\delta) = \frac{\lambda\kappa(1-\eta)(N-X)}{(\kappa + r + \lambda\eta N_s)(\kappa + \lambda N_s)}\int_\delta^{\bar\Delta}[1-F(x)]\,dx, \qquad N_s = N_s(F(\delta)) \text{ from (64)}.$$
--   Then
--
--   1. $\mathrm{rhs}_{21}(\bar\Delta) = 0$ and $\mathrm{rhs}_{21}$ is nonincreasing on $[0,\bar\Delta]$;
--   2. for every $0 < c \le \mathrm{rhs}_{21}(0)$ the equation $c = \mathrm{rhs}_{21}(\Delta_s)$ has exactly one solution $\Delta_s \in [0,\bar\Delta]$;
--   3. if $0 < c < c^*$, then in every steady-state intermediation equilibrium the seller cutoff solves (21): $c = \mathrm{rhs}_{21}(\Delta_s)$. This is the indifference condition $V_s(\Delta_s) = V_h(\Delta_s)$.
--
--   **Formalization Note** As for (20), the range $0 < c \le \mathrm{rhs}_{21}(0)$ in which the page's "unique solution in $[0,\bar\Delta]$" holds is stated explicitly.
-- source:
--   Shen, Wei & Yan, Financial Intermediation Chains in an OTC Market, MPRA Paper No. 74925 (version of October 29, 2016), p. 41 (PDF 44), proof of Theorem 1, Step II, (21); (21) stated p. 13 (PDF 16)

import Mathlib
import Definitions.Def_OTCChain_Equilibrium_Model
import Definitions.Def_OTCChain_Equilibrium_ClosedForm

namespace OTCChain.Equilibrium

open Set

/-- (21), proof of Theorem 1, Step II, p. 41: the right-hand side of (21) vanishes at
`∆s = ∆̄` and is nonincreasing on `[0, ∆̄]`; for every `0 < c ≤ rhs21(0)` the equation
`c = rhs21(∆s)` has exactly one solution in `[0, ∆̄]`; and in every intermediation equilibrium
(with `0 < c < c*`) the seller cutoff solves (21), i.e. `rhs21(∆s) = c` (indifference
`Vs(∆s) = Vh(∆s)`). -/
theorem eq_21 (M : Params) (hM : M.Standing) :
    rhs21 M M.Δbar = 0 ∧ AntitoneOn (rhs21 M) (Icc 0 M.Δbar) ∧
    (∀ c : ℝ, 0 < c → c ≤ rhs21 M 0 → ∃! δ, δ ∈ Icc 0 M.Δbar ∧ rhs21 M δ = c) ∧
    (0 < M.c → M.c < cStar M → ∀ (Δb Δs : ℝ) (μ : Densities) (V : Values),
      IsIntermEq M Δb Δs μ V → rhs21 M Δs = M.c) := by sorry

end OTCChain.Equilibrium
