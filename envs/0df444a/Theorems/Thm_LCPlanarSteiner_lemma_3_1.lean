-- Prove2me | Theorems.Thm_LCPlanarSteiner_lemma_3_1
-- name    : LCPlanarSteiner.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:03:27.61751+00:00
-- url     : https://prove2.me/theorems/1f0d80e6-9262-459f-a555-e19e5a4bcd7a
-- title:
--   Lemma 3.1 — tree-path separator: at most three root paths leave components of at most half the weight
-- statement:
--   Let $G$ be a planar graph on $n$ vertices, $T$ a spanning tree of $G$ with root $\rho$, and $w \ge 0$ vertex weights. A root path is the path of $T$ from $\rho$ to a vertex.
--
--   **Lemma 3.1 (Tree-path separator).** There is an algorithm, running in time polynomial in the binary input, that finds vertices $x_1, \dots, x_k$, $k \le 3$, such that deleting the union $X$ of the root paths from $\rho$ to $x_1, \dots, x_k$ leaves every connected component $K$ of $G - X$ with
--   $$
--   \sum_{v \in K} w(v) \le \frac12 \sum_{v} w(v).
--   $$
--
--   The separator is applied to the separator host in the rooted recursion of §3 and, with unit endpoint weights, in the planar extraction of Lemma 4.3.
--
--   **Formalization Note** The graph and the tree are given as edge lists, with planarity as a hypothesis; the algorithm is one function for all inputs, computed by a Turing machine (`Turing.TM2ComputableInPolyTime`) on a binary encoding.
--
--   Differences from the source:
--   - generalization: the input is a plane graph → the input is an edge list without an embedding, planarity being a hypothesis; reason: a planar embedding can be computed in polynomial time (Hopcroft–Tarjan 1974), so an algorithm for plane inputs gives one for edge lists, and the Lean statement specializes to the source's
--   - reading: found in polynomial time → one function computed by a Turing machine in time polynomial in the length of a fixed injective binary encoding; reason: the paper names no machine model
--   - encoding: a rooted spanning tree; at most three root paths; weak components → a subgraph T ≤ G with T.IsTree on all vertices and a root ρ; a list of at most three vertices x_j standing for the root paths ρ ⇝ x_j; connected components of G with the path vertices deleted; reason: Lean convention, same instances
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 3.1, p.5

import Mathlib
import Definitions.Def_LCPlanarSteiner_sgOf
import Definitions.Def_LCPlanarSteiner_rootPathSet
import Definitions.Def_LCPlanarSteiner_HalfSeparates
import Definitions.Def_LCPlanarSteiner_encSepIn
import Definitions.Def_ReserveLB_encListNat
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar

namespace LCPlanarSteiner

/-- **Lemma 3.1 (Tree-path separator [LT79, Tho04, FM23b]).**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 3.1, p.5: "Given a plane graph, a rooted spanning tree, and nonnegative vertex weights,
at most three root paths of the tree can be found in polynomial time whose deletion leaves weak
components of at most half the total weight."

There is a function `alg`, computable by a Turing machine in time polynomial in the binary input,
that maps a graph `G = sgOf n E`, a tree `T = sgOf n Tr`, a root `ρ` and weights `w` to a list of
at most three vertices `x₁, …` such that, whenever `G` is planar, `T` is a spanning tree of `G`,
`ρ` is a vertex and the weights are `n` nonnegative rationals, deleting the union of the root paths
of `T` from `ρ` to the `xⱼ` leaves components of `G` of weight at most half the total weight.

**Formalization Note.** The input is an edge list without an embedding (planarity is a hypothesis,
`IsPlanar`); the paper's input is a plane graph. A spanning tree is a subgraph `T ≤ G` on all
vertices with `T.IsTree`. The weight of a vertex `v` is the `v`-th entry of `w`. -/
theorem lemma_3_1 :
    ∃ alg : ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ × List ℚ → List ℕ,
      Nonempty (Turing.TM2ComputableInPolyTime encSepIn ReserveLB.encListNat alg) ∧
      ∀ (n : ℕ) (E Tr : List (ℕ × ℕ)) (ρ : ℕ) (w : List ℚ) (hρ : ρ < n),
        RobertsonSeymour1986.GM5.IsPlanar (sgOf n E) →
        sgOf n Tr ≤ sgOf n E → (sgOf n Tr).IsTree →
        w.length = n → (∀ a ∈ w, 0 ≤ a) →
        (alg (n, E, Tr, ρ, w)).length ≤ 3 ∧ (∀ x ∈ alg (n, E, Tr, ρ, w), x < n) ∧
        HalfSeparates (sgOf n E)
          {u | ∃ x ∈ alg (n, E, Tr, ρ, w), ∃ hx : x < n,
            u ∈ rootPathSet (sgOf n Tr) ⟨ρ, hρ⟩ ⟨x, hx⟩}
          (fun v => w.getD v.val 0) := by sorry

end LCPlanarSteiner
