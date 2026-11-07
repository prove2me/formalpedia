-- Prove2me | Theorems.Thm_IncrementalER_fact_3_4
-- name    : IncrementalER.fact_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:07:46.581726+00:00
-- url     : https://prove2.me/theorems/f7760c1a-858f-4c8a-a077-2a21ae202667
-- title:
--   Fact 3.4, p.11 — Schur complements preserve energies and resistances, raise conductances, and compose
-- statement:
--   Let $G=(V,E,c)$ be a connected graph, $S\subseteq V$, and $G_S=SC(G,S)$ its Schur complement upon $S$. Then:
--
--   1. for every demand $d\in\mathbb R^V$ (so $d^\top\mathbf 1=0$) supported on $S$, $d^\top L_G^\dagger d=d|_S^\top L_{G_S}^\dagger d|_S$;
--   2. for all $u,v\in S$, the effective resistance between $u$ and $v$ in $G_S$ equals that in $G$;
--   3. for all $u,v\in S$, $c_G(u,v)\le c_{G_S}(u,v)$;
--   4. for $S\subseteq T\subseteq V$, $SC(G,S)=SC(SC(G,T),S)$.
--
--   These standard facts let the paper replace $G$ by a Schur complement onto any terminal set containing the support of a query. Connectivity is the paper's standing assumption ("We assume throughout that everywhere we are dealing exclusively with connected graphs", p.10) and is a hypothesis.
--
--   Differences from the source:
--   - encoding: G = (V, E, c) an undirected capacitated multigraph (p.10) → a symmetric nonnegative conductance function with zero diagonal (parallel capacities added, no loops); reason: the Laplacian, effective resistances, leverage degrees and the random walk are unchanged by merging parallel edges; the paper's edges (u, v) join two vertices, and the source never uses loops
--   - encoding: G_S is a graph on S → G_S is a graph on V whose vertices outside S are isolated; the energy of d|_S in G_S is the energy of d; reason: isolated vertices change no energy or resistance between vertices of S
--   - encoding: SC(SC(G, T), S), with SC(G, T) a graph on T → eliminate T \ S from SC(G, T) (scCondRel _ T S); reason: SC(G, T) lives on T; eliminating all of V \ S from its representation on V would invert a singular block
--   - encoding: S ⊆ V (Definition 3.3 needs L_{S̄S̄} invertible) → S = ∅ allowed; then G_S has no edges; reason: every item is immediate for S = ∅; the case only fixes a value where the source's formula is undefined
--   - reading: item 1, "any demand d ∈ R^V with support only on S" → d supported on S with ∑ d = 0; reason: a demand is what a flow routes ("the electrical energy required to route those demands"), so it sums to zero (as in Theorem 1.1, d⊤1 = 0); for a vector with nonzero sum item 1 is false: one edge {1, 2} of conductance 1, S = {1}, d = 1₁ has energy 1/4 in G and 0 in G_S
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Fact 3.4, p.11; Definition 3.3, p.11; connectivity, p.10

import Mathlib
import Definitions.Def_IncrementalER_scCond

namespace IncrementalER

/-- **Fact 3.4** (Schur complements preserve energies and resistances, raise conductances, and
compose).

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), Fact 3.4, p.11; Definition 3.3, p.11; connectivity assumption, p.10.

For a connected graph `G` (conductance function `c`) and a set `S` of vertices, with `G_S` the
Schur complement graph:
1. every demand `d` (a vector with `d⊤1 = 0`) supported on `S` has the same energy in `G` and
   in `G_S`;
2. `Reff` between vertices of `S` is the same in `G` and `G_S`;
3. `c_G(u, v) ≤ c_{G_S}(u, v)` for `u, v ∈ S`;
4. for `S ⊆ T`, `SC(G, S) = SC(SC(G, T), S)`.

**Formalization Note.** `G_S` is a graph on all of `V` whose vertices outside `S` are isolated,
so the energy of `d|_S` in the graph on `S` is the energy of `d` in `G_S`. In item 4,
`SC(G, T)` lives on `T`, so `T \ S` is eliminated from it (`scCondRel _ T S`). `S = ∅` is allowed:
then `G_S` has no edges and every item is immediate. A *demand* is a vector with `d⊤1 = 0` (it
is routed by a flow, as item 1 says); for a vector with nonzero sum item 1 is false: on one edge
`{1, 2}` of conductance `1` with `S = {1}`, `d = 1₁` has energy `1/4` in `G` and `0` in `G_S`. -/
theorem fact_3_4 {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ) (hc : IsGraph c)
    (hconn : Connected c) (S : Finset V) :
    (∀ d : V → ℝ, (∀ x, x ∉ S → d x = 0) → ∑ x, d x = 0 →
        energy (lap c) d = energy (lap (scCond c S)) d) ∧
      (∀ u ∈ S, ∀ v ∈ S, reff (scCond c S) u v = reff c u v) ∧
      (∀ u ∈ S, ∀ v ∈ S, c u v ≤ scCond c S u v) ∧
      (∀ T : Finset V, S ⊆ T → scCond c S = scCondRel (scCond c T) T S) := by sorry

end IncrementalER
