-- Prove2me | Theorems.Thm_IDEPoA_active_shortest_of_small_volume
-- name    : IDEPoA.active_shortest_of_small_volume
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:44.09798+00:00
-- url     : https://prove2.me/theorems/981354d2-b600-48d3-9854-57a3eea7f9e3
-- title:
--   [15, Lemma 4.4] as used: small load on a shortest path forces active paths to be physically shortest
-- statement:
--   Let $f$ be a feasible flow, $v$ a node, $\theta\ge0$, and $P$ a physically shortest $v$-$t$ path carrying a flow volume of less than one at time $\theta$:
--   $$\sum_{e\in P}F_e^\Delta(\theta)<1.$$
--   Then every active $v$-$t$ path at time $\theta$ is physically shortest.
--
--   Since travel times are integers, a path that is physically longer than $P$ is longer by at least $1$, and a volume below $1$ on $P$ cannot make up for this. This is what confines a sink-like subgraph to shortest paths.
--
--   **Formalization Note** The paper cites this from Graf, Harks and Sering and gives no statement. It is stated here in the setting in which the paper applies it, with integer travel times and capacities. An active walk is a walk all of whose edges are active.
--
--   Differences from the source:
--   - generalization: directed graph G = (V, E) with edges vw → finite directed multigraph with tail and head maps, loops and parallel edges allowed; reason: a simple digraph is a special case
--   - reading: f+, f- integrable functions (p.7) → f+, f- integrable on every [0, T]; reason: F+ and F- only need the integral on [0, θ]; global integrability would exclude forever-cycling flows up front, and local integrability contains it
--   - encoding: rates on R≥0, constraints for θ ∈ R≥0 → rates ℝ → ℝ, constraints quantified over 0 ≤ θ; reason: values at negative times play no role
--   - encoding: node labels defined by the recursion (6) → label as the infimum of the costs of v-t walks; reason: same function for a feasible flow; the recursion is proved in a verification file
--   - reading: the paper cites [15, Lemma 4.4] without a statement: 'any such path always carries a flow volume of less than 1 ... By [15, Lemma 4.4] this means that all active v-t paths are also physically shortest' → the statement of that use, for a feasible flow and an active walk at one time; reason: [15] is a different paper; this is the claim the proofs here need
-- source:
--   Graf & Harks, The Price of Anarchy for Instantaneous Dynamic Equilibria, arXiv:2007.07794v2, [15, Lemma 4.4] as used in the proofs of Lemma 3.6, p.17, and Claim 3, p.20

import Mathlib
import Definitions.Def_IDEPoA_Model

open MeasureTheory Set
open scoped ENNReal

namespace IDEPoA

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- A physically shortest path with small load forces active paths to be physically shortest: the
form of [15, Lemma 4.4] (Graf, Harks, Sering, *Dynamic flows with adaptive route choice*) that
arXiv:2007.07794v2 uses on pp.17 and 20, in its integer setting ("we have vmin, τ∆ ≥ 1, since both
travel times and capacities are whole numbers here"). If a physically shortest `v`-`t` path `P`
carries a flow volume of less than `1` at time `θ`, then every active `v`-`t` walk at `θ` is
physically shortest. -/
theorem active_shortest_of_small_volume (N : FlowNetwork V E) (hN : Standing N) (f : Flow E)
    (hf : IsFeasible N f) (v : V) (θ : ℝ) (hθ : 0 ≤ θ) (P : List E) (hP : IsPhysShortest N v P)
    (hvol : (P.map fun e => load f e θ).sum < 1) (Q : List E) (hQ : IsActiveWalk N f θ v Q) :
    physLength N Q = physDist N v := by sorry

end IDEPoA
