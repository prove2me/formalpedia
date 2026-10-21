-- Prove2me | Theorems.Thm_OTCChain_Equilibrium_eq_55_57
-- name    : OTCChain.Equilibrium.eq_55_57
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:35.682213+00:00
-- url     : https://prove2.me/theorems/03880fcd-2c30-4c6e-9a3a-f709c0d19a80
-- title:
--   (55)–(57), proof of Theorem 1, Step I, p. 37 (PDF 40) — the steady-state densities below the buyer cutoff
-- statement:
--   Let the standing assumptions of the model hold and let $0 < \Delta_b < \Delta_s < \bar\Delta$. Let $(\mu_b,\mu_s,\mu_n,\mu_h)$ be a steady state for these cutoffs, i.e. satisfy (12)–(19), and let $N_b = \int_0^{\bar\Delta}\mu_b$. Then for every $\Delta \in [0,\Delta_b)$,
--   $$\mu_b(\Delta) = \mu_h(\Delta) = 0,\qquad \mu_n(\Delta) = \frac{\kappa(N-X) + \lambda N_b N}{\kappa + \lambda N_b} f(\Delta),\qquad \mu_s(\Delta) = \frac{\kappa X}{\kappa + \lambda N_b} f(\Delta).$$
--
--   Below the buyer cutoff, the steady state is therefore determined by the single number $N_b$; this is the first region of Step I of the proof of Theorem 1.
-- source:
--   Shen, Wei & Yan, Financial Intermediation Chains in an OTC Market, MPRA Paper No. 74925 (version of October 29, 2016), p. 37 (PDF 40), proof of Theorem 1, Step I, (55)–(57)

import Mathlib
import Definitions.Def_OTCChain_Equilibrium_Model
import Definitions.Def_OTCChain_Equilibrium_ClosedForm

namespace OTCChain.Equilibrium

open Set

/-- (55)–(57), proof of Theorem 1, Step I, p. 37: in a steady state with cutoffs
`0 < ∆b < ∆s < ∆̄`, on `[0, ∆b)` there are no buyers and no inactive holders, and the inactive
non-owner and seller densities are the multiples (56)–(57) of `f`, with `N_b = ∫₀^∆̄ μb`. -/
theorem eq_55_57 (M : Params) (hM : M.Standing) (Δb Δs : ℝ) (h0 : 0 < Δb) (h1 : Δb < Δs)
    (h2 : Δs < M.Δbar) (μ : Densities) (hμ : IsSteadyState M Δb Δs μ) :
    ∀ Δ ∈ Ico 0 Δb, μ.μb Δ = 0 ∧ μ.μh Δ = 0 ∧
      μ.μn Δ = (M.κ * (M.N - M.X) + M.lam * μ.Nb M * M.N) / (M.κ + M.lam * μ.Nb M) * M.f Δ ∧
      μ.μs Δ = M.κ * M.X / (M.κ + M.lam * μ.Nb M) * M.f Δ := by sorry

end OTCChain.Equilibrium
