-- Prove2me | Theorems.Thm_OTCChain_Equilibrium_eq_65_66_Nb
-- name    : OTCChain.Equilibrium.eq_65_66_Nb
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:35.12527+00:00
-- url     : https://prove2.me/theorems/bc78283d-9ea6-43e7-a4dc-5cffc3926b53
-- title:
--   (65)–(66), proof of Theorem 1, Step I, p. 38 (PDF 41) — N_b is the positive root of the quadratic (65)
-- statement:
--   Let the standing assumptions of the model hold, let $0 < \Delta_b < \Delta_s < \bar\Delta$, and let $\mu$ be a steady state for these cutoffs with buyer population $N_b = \int_0^{\bar\Delta}\mu_b$. Then $N_b$ solves (65),
--   $$N_b^2 + \Big(\frac{\kappa}{\lambda} - N + X + NF(\Delta_b)\Big)N_b - \frac{\kappa}{\lambda}(N-X)[1 - F(\Delta_b)] = 0,$$
--   and equals the root (66):
--   $$N_b = \frac{N - NF(\Delta_b) - X - \frac{\kappa}{\lambda}}{2} + \frac12\sqrt{\Big[N - NF(\Delta_b) - X - \frac{\kappa}{\lambda}\Big]^2 + 4\frac{\kappa}{\lambda}(N-X)[1 - F(\Delta_b)]}.$$
--
--   The buyer population depends on the buyer cutoff only through $F(\Delta_b)$; this closed form enters the cutoff equation (20).
-- source:
--   Shen, Wei & Yan, Financial Intermediation Chains in an OTC Market, MPRA Paper No. 74925 (version of October 29, 2016), p. 38 (PDF 41), proof of Theorem 1, Step I, (65)–(66)

import Mathlib
import Definitions.Def_OTCChain_Equilibrium_Model
import Definitions.Def_OTCChain_Equilibrium_ClosedForm

namespace OTCChain.Equilibrium

/-- (65)–(66), proof of Theorem 1, Step I, p. 38: in a steady state with cutoffs
`0 < ∆b < ∆s < ∆̄`, the buyer population `N_b = ∫₀^∆̄ μb` solves (65),
`N_b² + (κ/λ − N + X + N F(∆b)) N_b − (κ/λ)(N − X)[1 − F(∆b)] = 0`, and equals its root (66). -/
theorem eq_65_66_Nb (M : Params) (hM : M.Standing) (Δb Δs : ℝ) (h0 : 0 < Δb) (h1 : Δb < Δs)
    (h2 : Δs < M.Δbar) (μ : Densities) (hμ : IsSteadyState M Δb Δs μ) :
    μ.Nb M ^ 2 + (M.κ / M.lam - M.N + M.X + M.N * M.F Δb) * μ.Nb M
        - M.κ / M.lam * (M.N - M.X) * (1 - M.F Δb) = 0 ∧
      μ.Nb M = NbOf M (M.F Δb) := by sorry

end OTCChain.Equilibrium
