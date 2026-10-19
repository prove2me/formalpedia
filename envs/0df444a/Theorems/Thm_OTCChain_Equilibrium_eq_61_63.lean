-- Prove2me | Theorems.Thm_OTCChain_Equilibrium_eq_61_63
-- name    : OTCChain.Equilibrium.eq_61_63
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:46.417729+00:00
-- url     : https://prove2.me/theorems/e59dc2bc-7fb7-465f-a72a-c02b6338af34
-- title:
--   (61)–(63), proof of Theorem 1, Step I, p. 37 (PDF 40) — the steady-state densities above the seller cutoff
-- statement:
--   Let the standing assumptions of the model hold and let $0 < \Delta_b < \Delta_s < \bar\Delta$. Let $(\mu_b,\mu_s,\mu_n,\mu_h)$ be a steady state for these cutoffs, i.e. satisfy (12)–(19), and let $N_s = \int_0^{\bar\Delta}\mu_s$. Then for every $\Delta \in (\Delta_s,\bar\Delta]$,
--   $$\mu_n(\Delta) = \mu_s(\Delta) = 0,\qquad \mu_b(\Delta) = \frac{\kappa(N-X)}{\kappa + \lambda N_s} f(\Delta),\qquad \mu_h(\Delta) = \frac{\kappa X + \lambda N_s N}{\kappa + \lambda N_s} f(\Delta).$$
--
--   Above the seller cutoff the steady state is determined by $N_s$; together with (55)–(57) this reduces Step I to the two populations and the middle region.
-- source:
--   Shen, Wei & Yan, Financial Intermediation Chains in an OTC Market, MPRA Paper No. 74925 (version of October 29, 2016), p. 37 (PDF 40), proof of Theorem 1, Step I, (61)–(63)

import Mathlib
import Definitions.Def_OTCChain_Equilibrium_Model
import Definitions.Def_OTCChain_Equilibrium_ClosedForm

namespace OTCChain.Equilibrium

open Set

/-- (61)–(63), proof of Theorem 1, Step I, p. 37: in a steady state with cutoffs
`0 < ∆b < ∆s < ∆̄`, on `(∆s, ∆̄]` there are no inactive non-owners and no sellers, and the buyer
and inactive-holder densities are the multiples (62)–(63) of `f`, with `N_s = ∫₀^∆̄ μs`. -/
theorem eq_61_63 (M : Params) (hM : M.Standing) (Δb Δs : ℝ) (h0 : 0 < Δb) (h1 : Δb < Δs)
    (h2 : Δs < M.Δbar) (μ : Densities) (hμ : IsSteadyState M Δb Δs μ) :
    ∀ Δ ∈ Ioc Δs M.Δbar, μ.μn Δ = 0 ∧ μ.μs Δ = 0 ∧
      μ.μb Δ = M.κ * (M.N - M.X) / (M.κ + M.lam * μ.Ns M) * M.f Δ ∧
      μ.μh Δ = (M.κ * M.X + M.lam * μ.Ns M * M.N) / (M.κ + M.lam * μ.Ns M) * M.f Δ := by sorry

end OTCChain.Equilibrium
