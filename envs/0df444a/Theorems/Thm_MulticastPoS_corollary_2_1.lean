-- Prove2me | Theorems.Thm_MulticastPoS_corollary_2_1
-- name    : MulticastPoS.corollary_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:40:37.01228+00:00
-- url     : https://prove2.me/theorems/55550c87-b3fa-4634-98b5-dcda769a5991
-- title:
--   Corollary 2.1 — every global potential minimizer is a Nash equilibrium, and one exists
-- statement:
--   1. In every congestion game, every global minimizer $P$ of Rosenthal's potential $\Phi$ is a pure Nash equilibrium.
--   2. In the multicast game on a finite graph $G$ with sink $t$ and sources $s_i$, if every source is connected to $t$, then a global minimizer of $\Phi$ over the (finitely many) simple-path profiles exists.
--
--   This is the paper's route to a Nash equilibrium: the main theorem bounds the social cost of a global minimizer.
--
--   Differences from the source:
--   - generalization: Corollary 2.1 for the multicast Shapley game → clause 1 for every congestion game; reason: the proof uses only the exact-potential identity (3), which holds in every congestion game; the multicast game is an instance
--   - generalization: existence of a minimizer for the game with nonnegative costs → clause 2 for arbitrary real costs c; reason: only the finiteness of the set of simple-path profiles is used; nonnegative costs are a special case
--   - encoding: finite undirected graph G = (V, E); player i chooses a simple path P_i from s_i to t; n players → SimpleGraph on a Fintype V; strategies are the edge sets p.edges.toFinset of walks p : G.Walk (s i) t with p.IsPath; players a Fintype ι; reason: the same games: loops never lie on a simple path, a parallel edge is equivalent to a subdivided edge with costs c_e and 0 (same strategies, payments, potential and social cost), and payments, loads, Φ and SC depend on a path only through its edge set
--   - encoding: standing assumption: a path from each source to t exists (p.1) → hypothesis ∀ i, G.Reachable (s i) t in clause 2; reason: reachability is exactly the existence of an s_i–t walk, hence of a simple path
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), Corollary 2.1 and the paragraph after it, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_MulticastPoS_game
import Definitions.Def_MulticastPoS_IsGlobalMin

open CongestionPoA.AsymSum PriceOfStability.Harmonic

namespace MulticastPoS

/-- Corollary 2.1 and the existence remark after it (Huang–Yuan, *An O(log log n) Upper Bound on
the Price of Stability for Undirected Multicast Shapley Games*, STOC 2027 submission manuscript
(sha256 dd0e08d0…f6d4), p.5):

1. every global minimizer of the potential is a pure Nash equilibrium (stated for every
   congestion game, by Eq. (3));
2. if every source is connected to the sink, the multicast game `game G c t s` has a global
   minimizer of the potential (there are finitely many simple-path profiles).

**Formalization Note** Clause 1 is stated for every congestion game `Γ`, of which the multicast
game is an instance. -/
theorem corollary_2_1 :
    (∀ {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
      (Γ : CongestionGame ι E) (P : ι → Finset E), IsGlobalMin Γ P → IsPureNash Γ P) ∧
    (∀ {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
      (G : SimpleGraph V) (c : Sym2 V → ℝ) (t : V) (s : ι → V),
      (∀ i, G.Reachable (s i) t) → ∃ P, IsGlobalMin (game G c t s) P) := by sorry

end MulticastPoS
