-- Prove2me | Theorems.Thm_LiquidDemocracy_Upward_theorem_1
-- name    : LiquidDemocracy.Upward.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:28.5293+00:00
-- url     : https://prove2.me/theorems/65926005-34fc-432d-91a9-6f2b95b25510
-- title:
--   Theorem 1, p. 12 — the Upward Delegation Model satisfies probabilistic do no harm and positive gain for all continuous distributions
-- statement:
--   For every $p\in(0,1)$, the Upward Delegation Model $M^U_p$ — each voter delegates with probability $p$, to a strictly more competent voter chosen uniformly at random — satisfies both
--
--   1. **probabilistic do no harm** with respect to the class $\mathfrak D^C$ of all continuous distributions on $[0,1]$: for every $\mathcal D\in\mathfrak D^C$ and all $\varepsilon,\delta>0$ there is $n_0$ such that for all $n\ge n_0$
--   $$\mathbb P_{\mathcal D,M^U_p,n}\big[\mathrm{gain}(\vec p_n,G_n)\ge-\varepsilon\big]>1-\delta;$$
--   2. **probabilistic positive gain** with respect to $\mathfrak D^C$: there is $\mathcal D\in\mathfrak D^C$ such that for all $\varepsilon,\delta>0$ there is $n_0$ such that for all $n\ge n_0$
--   $$\mathbb P_{\mathcal D,M^U_p,n}\big[\mathrm{gain}(\vec p_n,G_n)\ge1-\varepsilon\big]>1-\delta.$$
--
--   Here $\mathrm{gain}(\vec p_n,G_n)$ is the probability that liquid democracy (weighted votes along the delegation graph $G_n$) decides correctly by strict majority minus the probability that direct democracy does. The theorem says that, under this simple model of upward delegation, liquid democracy is asymptotically never worse than direct democracy and can be strictly better.
--
--   **Formalization Note** "Continuous distribution" is read as continuous CDF, which for a probability measure on $\mathbb R$ means atomless; together with the standing assumption of p. 10 the class $\mathfrak D^C$ consists of atomless probability measures with support in $[0,1]$. The endpoints $p=0,1$ are excluded, as on the page.
-- source:
--   Berinsky et al., Tracking Truth with Liquid Democracy, arXiv:2107.11868v3, p. 12, Theorem 1

import Mathlib
import Definitions.Def_LiquidDemocracy_Upward_Setting

namespace LiquidDemocracy.Upward

/-- Theorem 1, p. 12 (Upward Delegation Model): for all `p ∈ (0,1)`, `M^U_p` satisfies probabilistic
do no harm and probabilistic positive gain with respect to the class `𝔇^C` of all continuous
distributions. -/
theorem theorem_1 (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    ProbDNH (upward p) ContClass ∧ ProbPG (upward p) ContClass := by sorry

end LiquidDemocracy.Upward
