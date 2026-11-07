-- Prove2me | Theorems.Thm_IncrementalER_fact_3_6
-- name    : IncrementalER.fact_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:07:37.385225+00:00
-- url     : https://prove2.me/theorems/4f2c0934-6b2c-4aa1-a476-1e019a862e72
-- title:
--   Fact 3.6, p.12 — $\ell^G(v)=\mathbb E[\deg_T(v)]$, $\ell^G(v)\le\deg(v)$, and Foster's identity
-- statement:
--   Let $G=(V,E,c)$ be a connected graph with leverage degrees $\ell^G(v)$. Then:
--
--   1. if $T$ is a random spanning tree of $G$ sampled with probability proportional to its capacity $c(T)=\prod_{e\in T}c(e)$, then $\ell^G(v)=\mathbb E[\deg_T(v)]$;
--   2. $\ell^G(v)\le\deg(v)$ for every $v\in V$;
--   3. (Foster's identity)
--   $$\sum_{v\in V}\ell^G(v)=2(|V|-1).$$
--
--   Foster's identity is the budget behind the paper's averaging arguments (Lemmas 4.4 and 4.8). Connectivity is the paper's standing assumption ("We assume throughout that everywhere we are dealing exclusively with connected graphs", p.10) and is a hypothesis.
--
--   Differences from the source:
--   - encoding: G = (V, E, c) an undirected capacitated multigraph (p.10) → a symmetric nonnegative conductance function with zero diagonal (parallel capacities added, no loops); reason: the Laplacian, effective resistances, leverage degrees and the random walk are unchanged by merging parallel edges; the paper's edges (u, v) join two vertices, and the source never uses loops
--   - generalization: deg(v) = |{e ∈ E : v ∈ e}| (multigraph degree, p.10) → deg(v) = number of distinct neighbours of v; reason: this is at most the multigraph degree, so item 2 in Lean implies the multigraph item 2
--   - encoding: uniform spanning tree of the multigraph, sampled proportional to ∏ c(e) → spanning trees of the merged graph as sets of vertex pairs, capacity ∏ c(e); reason: the law of the tree's vertex degrees is the same, since a merged conductance is the sum of the parallel capacities
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Fact 3.6, p.12; Definition 3.5, p.12; connectivity, p.10

import Mathlib
import Definitions.Def_IncrementalER_lap
import Definitions.Def_IncrementalER_ustExpDeg

namespace IncrementalER

/-- **Fact 3.6** (leverage degree: random spanning tree degree, degree bound, Foster's identity).

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), Fact 3.6, p.12; Definition 3.5, p.12; connectivity assumption, p.10.

For a connected graph `G = (V, E, c)`:
1. `ℓ^G(v) = E[deg_T(v)]` for a spanning tree `T` drawn with probability proportional to
   `c(T) = ∏_{e ∈ T} c(e)`;
2. `ℓ^G(v) ≤ deg(v)` for every `v`;
3. `∑_v ℓ^G(v) = 2(|V| − 1)` (Foster's identity).

**Formalization Note.** The graph is its collapsed conductance function, so `deg(v)` in item 2
counts distinct neighbours, which is at most the multigraph degree: item 2 is then at least as
strong as for the multigraph. -/
theorem fact_3_6 {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ) (hc : IsGraph c)
    (hconn : Connected c) :
    (∀ v, levDeg c v = ustExpDeg c v) ∧ (∀ v, levDeg c v ≤ deg c v) ∧
      ∑ v, levDeg c v = 2 * ((Fintype.card V : ℝ) - 1) := by sorry

end IncrementalER
