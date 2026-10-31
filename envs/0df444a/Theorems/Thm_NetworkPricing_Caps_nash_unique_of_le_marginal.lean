-- Prove2me | Theorems.Thm_NetworkPricing_Caps_nash_unique_of_le_marginal
-- name    : NetworkPricing.Caps.nash_unique_of_le_marginal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:16:40.626116+00:00
-- url     : https://prove2.me/theorems/27c954bd-7698-45d6-b064-4ee676ab887a
-- title:
--   Proof of Theorem 1, p. 8 — with caps t̄ ≤ t̂, every capped Nash equilibrium equals t̄
-- statement:
--   Consider an instance of the network pricing game satisfying the standing assumptions of §2.1 and having unique Wardrop link flows for all tolls $t \ge 0$, let $x(t)$ be a selection of Wardrop flows, and write $\pi_e(t) = t_e\,x_e(t)$. Let $\bar t$ be an optimal toll vector (with optimal flow $x^*$) such that $\bar t \le \hat t$, where $\hat t_e = x^*_e\,\ell'_e(x^*_e)$ are the marginal tolls.
--
--   If $t$ is a Nash equilibrium of the game with caps $\bar t$ — that is, $0 \le t \le \bar t$ and for every $e$ and every $s_e \in [0, \bar t_e]$,
--
--   $$
--   \pi_e(s_e, t_{-e}) \le \pi_e(t),
--   $$
--
--   then $t = \bar t$.
--
--   This is the uniqueness half of Theorem 1.
-- source:
--   Correa, Guzmán, Lianeas, Nikolova & Schröder, Network Pricing: How to Induce Optimal Flows Under Strategic Link Operators, Operations Research (Articles in Advance, 2021), doi:10.1287/opre.2020.2067, proof of Theorem 1, p. 8, "Now, we show that there is a unique Nash equilibrium"

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_NetworkPricing_Caps_Model

namespace NetworkPricing.Caps

open KellyStochasticNetworks

theorem nash_unique_of_le_marginal {J R Sd : ℕ} (I : Instance J R Sd) (hI : I.Standing) (hU : I.UniqueWardrop)
    (flow : (Fin J → ℝ) → Fin R → ℝ) (hflow : ∀ t : Fin J → ℝ, 0 ≤ t → I.IsWardropFlow t (flow t))
    (tbar : Fin J → ℝ) (fstar : Fin R → ℝ) (hopt : I.IsOptimalToll flow fstar tbar)
    (hcap : ∀ e, tbar e ≤ I.marginalToll fstar e) :
    ∀ t : Fin J → ℝ, I.IsCappedNash flow tbar t → t = tbar := by sorry

end NetworkPricing.Caps
