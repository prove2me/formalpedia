-- Prove2me | Theorems.Thm_MulticastPoS_lemma_2_2
-- name    : MulticastPoS.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:40:39.95023+00:00
-- url     : https://prove2.me/theorems/be04c0f3-8b68-4a4b-b239-4b78c9f5de2c
-- title:
--   Lemma 2.2 — existence of a tree-supported global minimizer
-- statement:
--   Let the edge costs be nonnegative and $E_0=\{e : c_e=0\}$. For every global minimizer $\hat P$ of the potential $\Phi$ there is a global minimizer $P$ whose support is a tree and such that
--
--   $$
--   P_i\setminus E_0=\hat P_i\setminus E_0\quad\text{for every player } i. \tag{4}
--   $$
--
--   Consequently $\Phi(P)=\Phi(\hat P)$ and $SC(P)=SC(\hat P)$.
--
--   The lemma lets the analysis work on a tree (the Nash tree $T=\operatorname{supp}(P)$) without changing the social cost of the minimizer.
--
--   Differences from the source:
--   - encoding: finite undirected graph G = (V, E); player i chooses a simple path P_i from s_i to t; n players → SimpleGraph on a Fintype V; strategies are the edge sets p.edges.toFinset of walks p : G.Walk (s i) t with p.IsPath; players a Fintype ι; reason: the same games: loops never lie on a simple path, a parallel edge is equivalent to a subdivided edge with costs c_e and 0 (same strategies, payments, potential and social cost), and payments, loads, Φ and SC depend on a path only through its edge set
--   - encoding: a nonnegative cost c_e on each edge e → c : Sym2 V → ℝ with 0 ≤ c e for every e ∈ G.edgeSet; reason: the values of c off the graph never enter: no strategy contains a non-edge
--   - encoding: standing assumption: a path from each source to t exists (p.1) → not a separate hypothesis; reason: it is implied by the hypothesis that a (global-minimizer) profile exists, since every player then has an s_i–t path
--   - encoding: the support of P is a tree → IsTreeSupported P: the support edges form an acyclic graph; reason: the support of a path profile is connected through t, so acyclic is the same as a tree; the empty support is the degenerate tree {t} of Appendix A
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), Lemma 2.2, p.5 (PDF p.6); proof Appendix A, pp.13–14

import Mathlib
import Definitions.Def_MulticastPoS_game
import Definitions.Def_MulticastPoS_socialCost
import Definitions.Def_MulticastPoS_IsTreeSupported
import Definitions.Def_MulticastPoS_IsGlobalMin

open CongestionPoA.AsymSum PriceOfStability.Harmonic

namespace MulticastPoS

/-- Lemma 2.2, existence of a tree-supported global minimizer (Huang–Yuan, *An O(log log n) Upper
Bound on the Price of Stability for Undirected Multicast Shapley Games*, STOC 2027 submission
manuscript (sha256 dd0e08d0…f6d4), p.5; proof in Appendix A, pp.13–14): with nonnegative edge
costs, for every global minimizer `P̂` of `Φ` there is a global minimizer `P` whose support is a
tree and with `Pᵢ \ E₀ = P̂ᵢ \ E₀` for every player `i` (4), where `E₀ = {e : c_e = 0}`;
consequently `Φ(P) = Φ(P̂)` and `SC(P) = SC(P̂)`.

**Formalization Note** `Pᵢ \ E₀` is the filter of `Pᵢ` by `c e ≠ 0`. Costs are assumed
nonnegative on the edges of `G` only. -/
theorem lemma_2_2 {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph V) (c : Sym2 V → ℝ) (t : V) (s : ι → V)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (Phat : ι → Finset (Sym2 V))
    (hPhat : IsGlobalMin (game G c t s) Phat) :
    ∃ P, IsGlobalMin (game G c t s) P ∧ IsTreeSupported P ∧
      (∀ i, (P i).filter (fun e => c e ≠ 0) = (Phat i).filter (fun e => c e ≠ 0)) ∧
      potential (game G c t s) P = potential (game G c t s) Phat ∧
      socialCost c P = socialCost c Phat := by sorry

end MulticastPoS
