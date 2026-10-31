-- Prove2me | Theorems.Thm_NetworkPricing_Caps_lemma_2
-- name    : NetworkPricing.Caps.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:16:33.408294+00:00
-- url     : https://prove2.me/theorems/c645ff3f-3429-4731-89c5-569cf0ec3dde
-- title:
--   Lemma 2, p. 7 — at a locally profit-maximizing toll, x_e(t)·ℓ′_e(x_e(t)) ≤ t_e
-- statement:
--   Consider an instance of the network pricing game satisfying the standing assumptions of §2.1 and having unique Wardrop link flows for all tolls $t \ge 0$, and let $x(t)$ be a selection of Wardrop flows. The profit of operator $e$ is $\pi_e(t) = t_e\,x_e(t)$.
--
--   Let $t \ge 0$ be a toll vector and $e$ a link. If $t_e$ is a local maximizer of $s_e \mapsto \pi_e(s_e, t_{-e})$ over $s_e \ge 0$, then
--
--   $$
--   x_e(t)\,\ell_e'\big(x_e(t)\big) \le t_e .
--   $$
--
--   In words: at a (local) profit maximum, an operator's toll is at least the marginal congestion cost its users impose. This inequality is the key step of the uniqueness part of Theorem 1.
--
--   **Formalization Note** "Local optimum for the profit-maximization problem" is read as a local maximum of $s_e \mapsto \pi_e(s_e, t_{-e})$ relative to the operator's feasible tolls $s_e \ge 0$. $\ell'_e$ is the derivative of the differentiable latency $\ell_e$.
-- source:
--   Correa, Guzmán, Lianeas, Nikolova & Schröder, Network Pricing: How to Induce Optimal Flows Under Strategic Link Operators, Operations Research (Articles in Advance, 2021), doi:10.1287/opre.2020.2067, Lemma 2, p. 7

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_NetworkPricing_Caps_Model

namespace NetworkPricing.Caps

open KellyStochasticNetworks

theorem lemma_2 {J R Sd : ℕ} (I : Instance J R Sd) (hI : I.Standing) (hU : I.UniqueWardrop)
    (flow : (Fin J → ℝ) → Fin R → ℝ) (hflow : ∀ t : Fin J → ℝ, 0 ≤ t → I.IsWardropFlow t (flow t))
    (t : Fin J → ℝ) (ht : 0 ≤ t) (e : Fin J)
    (hloc : IsLocalMaxOn (fun s : ℝ => I.profit flow (Function.update t e s) e) (Set.Ici 0) (t e)) :
    linkFlow I.A (flow t) e * deriv (I.ℓ e) (linkFlow I.A (flow t) e) ≤ t e := by sorry

end NetworkPricing.Caps
