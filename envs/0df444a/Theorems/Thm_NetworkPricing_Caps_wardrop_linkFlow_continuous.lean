-- Prove2me | Theorems.Thm_NetworkPricing_Caps_wardrop_linkFlow_continuous
-- name    : NetworkPricing.Caps.wardrop_linkFlow_continuous
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:16:31.121888+00:00
-- url     : https://prove2.me/theorems/a5d8dc5b-ce47-4c0d-a7c9-0b8a1e86438d
-- title:
--   §2.1.2, p. 5 — the Wardrop link flows x_e(t) are continuous in the tolls t ≥ 0
-- statement:
--   Consider an instance of the network pricing game satisfying the standing assumptions of §2.1 (nonincreasing continuous nonnegative utilities $u_k$ on $[0, r_k]$; nondecreasing, convex, nonnegative, differentiable latencies $\ell_e$) in which the Wardrop flow is unique linkwise for every toll vector $t \ge 0$. Let $t \mapsto x(t)$ be any selection of Wardrop flows, i.e. $x(t)$ maximizes the potential (1) over the set $X$ of flows for every $t \ge 0$. Then for every link $e$, the link flow
--
--   $$
--   t \longmapsto x_e(t)
--   $$
--
--   is continuous on the orthant $\{t \in \mathbb R^E : t \ge 0\}$.
--
--   This is the continuity of the induced Wardrop flow that the proof of Lemma 2 uses.
--
--   **Formalization Note** The page attributes the claim to Berge's maximum theorem. The selection $x(t)$ is arbitrary; only its link flows enter the statement, and these are uniquely determined by the uniqueness hypothesis.
-- source:
--   Correa, Guzmán, Lianeas, Nikolova & Schröder, Network Pricing: How to Induce Optimal Flows Under Strategic Link Operators, Operations Research (Articles in Advance, 2021), doi:10.1287/opre.2020.2067, §2.1.2, p. 5, "(x_e(t))_{e∈E} is a well-defined function that is moreover continuous by Berge's (1963) theorem"

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_NetworkPricing_Caps_Model

namespace NetworkPricing.Caps

open KellyStochasticNetworks

theorem wardrop_linkFlow_continuous {J R Sd : ℕ} (I : Instance J R Sd) (hI : I.Standing) (hU : I.UniqueWardrop)
    (flow : (Fin J → ℝ) → Fin R → ℝ) (hflow : ∀ t : Fin J → ℝ, 0 ≤ t → I.IsWardropFlow t (flow t)) :
    ∀ e : Fin J, ContinuousOn (fun t : Fin J → ℝ => linkFlow I.A (flow t) e) {t | 0 ≤ t} := by sorry

end NetworkPricing.Caps
