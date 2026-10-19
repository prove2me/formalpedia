-- Prove2me | Theorems.Thm_OTCChain_Equilibrium_eq_64_Ns
-- name    : OTCChain.Equilibrium.eq_64_Ns
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:38.352732+00:00
-- url     : https://prove2.me/theorems/eff83601-9793-4bdc-856b-7eb5bdfe0d20
-- title:
--   (64), proof of Theorem 1, Step I, p. 38 (PDF 41) — market clearing makes N_s the positive root of a quadratic
-- statement:
--   Let the standing assumptions of the model hold, let $0 < \Delta_b < \Delta_s < \bar\Delta$, and let $\mu$ be a steady state for these cutoffs with seller population $N_s = \int_0^{\bar\Delta}\mu_s$. Then
--   $$N_s^2 + \Big(\frac{\kappa}{\lambda} + N - X - NF(\Delta_s)\Big)N_s - \frac{\kappa X}{\lambda}F(\Delta_s) = 0,$$
--   and $N_s$ is the root (64):
--   $$N_s = \frac12\sqrt{\Big[\frac{\kappa}{\lambda} + N - X - NF(\Delta_s)\Big]^2 + 4\frac{\kappa X}{\lambda}F(\Delta_s)} - \frac12\Big[\frac{\kappa}{\lambda} + N - X - NF(\Delta_s)\Big].$$
--
--   The seller population thus depends on the seller cutoff only through $F(\Delta_s)$; this closed form enters the cutoff equation (21).
-- source:
--   Shen, Wei & Yan, Financial Intermediation Chains in an OTC Market, MPRA Paper No. 74925 (version of October 29, 2016), p. 38 (PDF 41), proof of Theorem 1, Step I, (64)

import Mathlib
import Definitions.Def_OTCChain_Equilibrium_Model
import Definitions.Def_OTCChain_Equilibrium_ClosedForm

namespace OTCChain.Equilibrium

/-- (64), proof of Theorem 1, Step I, p. 38: in a steady state with cutoffs `0 < ∆b < ∆s < ∆̄`,
the seller population `N_s = ∫₀^∆̄ μs` solves
`N_s² + (κ/λ + N − X − N F(∆s)) N_s − (κX/λ) F(∆s) = 0` and equals its root (64). -/
theorem eq_64_Ns (M : Params) (hM : M.Standing) (Δb Δs : ℝ) (h0 : 0 < Δb) (h1 : Δb < Δs)
    (h2 : Δs < M.Δbar) (μ : Densities) (hμ : IsSteadyState M Δb Δs μ) :
    μ.Ns M ^ 2 + (M.κ / M.lam + M.N - M.X - M.N * M.F Δs) * μ.Ns M
        - M.κ * M.X / M.lam * M.F Δs = 0 ∧
      μ.Ns M = NsOf M (M.F Δs) := by sorry

end OTCChain.Equilibrium
