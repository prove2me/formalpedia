-- Prove2me | Theorems.Thm_NetworkPricing_Caps_theorem_1
-- name    : NetworkPricing.Caps.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:16:49.530237+00:00
-- url     : https://prove2.me/theorems/f7bebf34-619d-4897-bb0b-c44a43292c5c
-- title:
--   Theorem 1, p. 7 — an optimal toll vector t̄ ≤ t̂ (marginal tolls) is a (strong) cap equilibrium
-- statement:
--   Consider an instance of the network pricing game with elastic demand: utilities $u_k$ nonincreasing, continuous and nonnegative on $[0, r_k]$; latencies $\ell_e$ nondecreasing, convex, nonnegative and differentiable; and unique Wardrop link flows for every toll vector $t \ge 0$. Let $x(t)$ be a selection of Wardrop flows, so that operator $e$ earns $\pi_e(t) = t_e\,x_e(t)$.
--
--   Let $\bar t$ be an optimal toll vector — $\bar t \ge 0$ and $x(\bar t)$ has the link flows of an optimal flow $x^*$ — such that
--
--   $$
--   \bar t_e \le \hat t_e = x^*_e\,\ell'_e(x^*_e) \quad \text{for every link } e .
--   $$
--
--   Then $\bar t$ is a cap equilibrium and a strong cap equilibrium: when every operator $e$ is restricted to tolls $s_e \in [0, \bar t_e]$, the profile $\bar t$ is the unique Nash equilibrium and also the unique strong Nash equilibrium.
--
--   Since $\bar t$ is optimal, such caps are great tolls: regulated by price caps alone, competing link operators settle on tolls that induce the socially optimal flow.
--
--   **Formalization Note** "(strong)" is read as both notions of Definition 1a, stated as a conjunction. Strong Nash equilibria are with respect to nonempty coalitions. Routes are an abstract 0/1 route system; "smooth" is read as differentiable.
-- source:
--   Correa, Guzmán, Lianeas, Nikolova & Schröder, Network Pricing: How to Induce Optimal Flows Under Strategic Link Operators, Operations Research (Articles in Advance, 2021), doi:10.1287/opre.2020.2067, Theorem 1, p. 7

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_NetworkPricing_Caps_Model

namespace NetworkPricing.Caps

open KellyStochasticNetworks

theorem theorem_1 {J R Sd : ℕ} (I : Instance J R Sd) (hI : I.Standing) (hU : I.UniqueWardrop)
    (flow : (Fin J → ℝ) → Fin R → ℝ) (hflow : ∀ t : Fin J → ℝ, 0 ≤ t → I.IsWardropFlow t (flow t))
    (tbar : Fin J → ℝ) (fstar : Fin R → ℝ) (hopt : I.IsOptimalToll flow fstar tbar)
    (hcap : ∀ e, tbar e ≤ I.marginalToll fstar e) :
    I.IsCapEquilibrium flow tbar ∧ I.IsStrongCapEquilibrium flow tbar := by sorry

end NetworkPricing.Caps
