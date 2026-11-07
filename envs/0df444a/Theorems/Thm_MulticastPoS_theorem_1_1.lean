-- Prove2me | Theorems.Thm_MulticastPoS_theorem_1_1
-- name    : MulticastPoS.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:41:12.355071+00:00
-- url     : https://prove2.me/theorems/142b3524-06de-419d-90ad-86b9da01cb8b
-- title:
--   Theorem 1.1 — every undirected multicast Shapley game has a Nash equilibrium with $SC(P)=O(\log\log n)\,OPT$
-- statement:
--   Every undirected multicast Shapley network design game with $n$ players admits a Nash equilibrium $P$ satisfying
--
--   $$
--   SC(P)=O(\log\log n)\,OPT .
--   $$
--
--   Thus the price of stability is $O(\log\log n)$. Precisely:
--
--   1. For every finite undirected graph with nonnegative edge costs, every sink $t$ and every finite set of $n$ players whose sources are connected to $t$, some pure Nash equilibrium $P$ satisfies
--   $$
--   SC(P)\le 10\bigl(1+\lfloor\log_2\log_2 n\rfloor\bigr)\,SC(Q)\quad\text{for every path profile } Q .
--   $$
--   2. There is a constant $C>0$ such that every such game with $n\ge 3$ players has a pure Nash equilibrium $P$ with
--   $$
--   SC(P)\le C\,\log\log n\cdot SC(Q)\quad\text{for every path profile } Q .
--   $$
--
--   Here $SC$ is the total cost of the used edges and $OPT$, the least social cost, equals the cost of a cheapest tree connecting all sources to $t$. This improves the $O(\log n/\log\log n)$ bound of Li (2009) exponentially.
--
--   **Formalization Note** $\log$ in clause 2 is the natural logarithm; $\lfloor\log_2\log_2 n\rfloor$ is `Nat.log 2 (Nat.log 2 n)`.
--
--   Differences from the source:
--   - encoding: finite undirected graph G = (V, E); player i chooses a simple path P_i from s_i to t; n players → SimpleGraph on a Fintype V; strategies are the edge sets p.edges.toFinset of walks p : G.Walk (s i) t with p.IsPath; players a Fintype ι; reason: the same games: loops never lie on a simple path, a parallel edge is equivalent to a subdivided edge with costs c_e and 0 (same strategies, payments, potential and social cost), and payments, loads, Φ and SC depend on a path only through its edge set
--   - encoding: a nonnegative cost c_e on each edge e → c : Sym2 V → ℝ with 0 ≤ c e for every e ∈ G.edgeSet; reason: the values of c off the graph never enter: no strategy contains a non-edge
--   - encoding: standing assumption: a path from each source to t exists (p.1) → hypothesis ∀ i, G.Reachable (s i) t; reason: reachability is exactly the existence of an s_i–t path
--   - encoding: OPT = c(T⋆), the cost of a fixed minimum-cost tree connecting all sources to t → the bound holds against SC(Q) for every path profile Q; reason: there are finitely many profiles and, by the optimum-as-tree milestone, the least SC(Q) equals OPT, so 'for every Q' is equivalent
--   - generalization: SC(P) = O(log log n) OPT → clause 1: SC(P) ≤ 10 (1 + Nat.log 2 (Nat.log 2 n)) SC(Q); reason: the explicit bound is what the proof on p.6 gives and implies the O-bound
--   - reading: O(log log n) → clause 2: one constant C > 0, uniform over all games with n ≥ 3 players; reason: n ≥ 3 makes log log n > 0; a uniform constant is the standard meaning of the O-bound over all games
--   - encoding: all finite graphs and player sets → vertex and player types in Type (universe 0); reason: every finite game is isomorphic to one on types in Type, and the statement is invariant under isomorphism
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), Theorem 1.1, p.1 (PDF p.2); proof p.6 (PDF p.7)

import Mathlib
import Definitions.Def_MulticastPoS_game
import Definitions.Def_MulticastPoS_socialCost

open CongestionPoA.AsymSum PriceOfStability.Harmonic

namespace MulticastPoS

/-- Theorem 1.1, main theorem (Huang–Yuan, *An O(log log n) Upper Bound on the Price of Stability
for Undirected Multicast Shapley Games*, STOC 2027 submission manuscript (sha256 dd0e08d0…f6d4),
p.1; proof p.6): every undirected multicast Shapley network design game with `n` players admits
a Nash equilibrium `P` satisfying `SC(P) = O(log log n) OPT`. Thus the price of stability is
`O(log log n)`. Stated as two clauses:

1. for every finite undirected graph with nonnegative edge costs, every sink and every finite set
   of players whose sources are connected to the sink, some pure Nash equilibrium `P` satisfies
   `SC(P) ≤ 10 (1 + ⌊log₂ log₂ n⌋) SC(Q)` for every path profile `Q`;
2. there is one constant `C > 0` such that every such game with `n ≥ 3` players has a pure Nash
   equilibrium `P` with `SC(P) ≤ C log log n · SC(Q)` for every path profile `Q`.

**Formalization Note** Graphs are `SimpleGraph`s on finite vertex types in `Type`, players a
finite type in `Type` with `n = Fintype.card ι`, strategies the edge sets of simple
source–sink paths. `OPT`, the minimum social cost (equal to the cost of a cheapest tree through
`t` and all sources), is expressed by quantifying over every profile `Q`. Costs are nonnegative
on the edges of `G`; their values off the graph never enter. `⌊log₂ log₂ n⌋` is
`Nat.log 2 (Nat.log 2 n)` and `log` in clause 2 is the natural logarithm. -/
theorem theorem_1_1 :
    (∀ (V ι : Type) [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
      (G : SimpleGraph V) (c : Sym2 V → ℝ) (t : V) (s : ι → V),
      (∀ e ∈ G.edgeSet, 0 ≤ c e) → (∀ i, G.Reachable (s i) t) →
      ∃ P, IsPureNash (game G c t s) P ∧
        ∀ Q, IsProfile (game G c t s) Q →
          socialCost c P ≤
            10 * ((1 + Nat.log 2 (Nat.log 2 (Fintype.card ι)) : ℕ) : ℝ) * socialCost c Q) ∧
    ∃ C : ℝ, 0 < C ∧
      ∀ (V ι : Type) [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
        (G : SimpleGraph V) (c : Sym2 V → ℝ) (t : V) (s : ι → V),
        (∀ e ∈ G.edgeSet, 0 ≤ c e) → (∀ i, G.Reachable (s i) t) → 3 ≤ Fintype.card ι →
        ∃ P, IsPureNash (game G c t s) P ∧
          ∀ Q, IsProfile (game G c t s) Q →
            socialCost c P ≤
              C * Real.log (Real.log (Fintype.card ι)) * socialCost c Q := by sorry

end MulticastPoS
