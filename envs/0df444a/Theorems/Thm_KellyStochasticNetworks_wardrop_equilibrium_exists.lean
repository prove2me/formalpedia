-- Prove2me | Theorems.Thm_KellyStochasticNetworks_wardrop_equilibrium_exists
-- name    : KellyStochasticNetworks.wardrop_equilibrium_exists
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T16:01:32.784949+00:00
-- url     : https://prove2.me/theorems/95c2a92e-c9c5-4867-bedd-b9ec39b7654a
-- title:
--   Theorem 4.3 — a Wardrop equilibrium exists
-- statement:
--   Model a road network as a set of $J$ directed links. Routes are subsets of links, recorded by
--   a link-route incidence matrix $A$ with entries $0$ and $1$; each route $r$ serves a single
--   source–destination pair $s(r)$; and $f_\sigma \ge 0$ is the flow to be carried between pair
--   $\sigma$. Each link has a delay function $D_j$, continuous and increasing, and the delay along
--   route $r$ at route flows $x$ is $\sum_j D_j(y_j)A_{jr}$ with $y = Ax$.
--
--   Suppose every source–destination pair is served by at least one route. Then a **Wardrop
--   equilibrium** exists: there is a feasible vector of route flows $x$ — non-negative, with the
--   flows on the routes serving $\sigma$ summing to $f_\sigma$ — such that
--   $$x_r > 0 \implies \sum_j D_j(y_j)A_{jr} = \min_{r' \in s(r)}\sum_j D_j(y_j)A_{jr'} .$$
--   Every route actually carrying traffic is, in delay, a shortest route for the traffic it
--   carries, so no driver has an incentive to switch.
--
--   Existence is what makes the model describe anything at all. It is not accompanied by a
--   uniqueness claim — the equilibrium route flows need not be unique, though the link loads are —
--   nor by any efficiency claim: Braess's paradox says the equilibrium can be worse for everyone
--   than a routing pattern that a planner could impose.
--
--   **Formalization Note** The two hypotheses beyond the model are exactly what make the feasible
--   set non-empty: each flow requirement is non-negative, and each source–destination pair is
--   served by some route. The equilibrium condition is written as an inequality against every
--   route serving the same pair, which is the displayed minimum with the minimum written out.
--   Delay functions are total and monotone in the weak sense, which excludes the vertical asymptote
--   that Figure 4.5 permits.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, pp. 96-97 (PDF pp. 104-105), Definition 4.2 and Theorem 4.3: 'Definition 4.2 A Wardrop equilibrium is a vector of flows along routes x = (x_r, r in R) such that x_r > 0 => sum_{j in J} D_j(y_j) A_{jr} = min_{r' in s(r)} sum_{j in J} D_j(y_j) A_{jr'}, where y = Ax. From our definition, it is not clear that a Wardrop equilibrium exists and how many of them there are. We will now show the existence of a Wardrop equilibrium, by exhibiting an alternative characterization of it. Theorem 4.3 A Wardrop equilibrium exists.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop

namespace KellyStochasticNetworks

theorem wardrop_equilibrium_exists {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (D : Fin J → ℝ → ℝ) (f : Fin Sd → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (hD : ∀ j, Continuous (D j)) (hmono : ∀ j, Monotone (D j))
    (hf : ∀ σ, 0 ≤ f σ) (hserved : ∀ σ, ∃ r, s r = σ) :
    ∃ x : Fin R → ℝ, IsWardropEquilibrium A s D f x := by sorry

end KellyStochasticNetworks
