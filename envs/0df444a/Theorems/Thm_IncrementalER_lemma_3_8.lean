-- Prove2me | Theorems.Thm_IncrementalER_lemma_3_8
-- name    : IncrementalER.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:08:03.067111+00:00
-- url     : https://prove2.me/theorems/9fb966d5-3fc3-4f66-9c65-c911df73063f
-- title:
--   Lemma 3.8 and (2), p.12 — $q^G_T(v)=q^G(v)+\sum_{u\notin T}q^G(u)\,p_u(\tau_v<\tau_{T\setminus\{v\}})$
-- statement:
--   Let $G=(V,E,c)$ be a connected graph and $T\subseteq V$. Then for every $v\in T$:
--
--   1. $q^G_T(v)=q^G(v)-\big(L_{T,V\setminus T}L^{-1}_{V\setminus T,V\setminus T}\,q^G|_{V\setminus T}\big)(v)$;
--   2. equivalently,
--   $$q^G_T(v)=q^G(v)+\sum_{u\in V\setminus T}q^G(u)\,p_u(\tau_v<\tau_{T\setminus\{v\}}),\tag{2}$$
--   where $p_u(\tau_v<\tau_{T\setminus\{v\}})$ is the probability that the random walk from $u$ reaches $v$ before $T\setminus\{v\}$.
--
--   The walk form is what the paper's leverage-degree estimator samples. Connectivity is the paper's standing assumption ("We assume throughout that everywhere we are dealing exclusively with connected graphs", p.10) and is a hypothesis.
--
--   Differences from the source:
--   - encoding: G = (V, E, c) an undirected capacitated multigraph (p.10) → a symmetric nonnegative conductance function with zero diagonal (parallel capacities added, no loops); reason: the Laplacian, effective resistances, leverage degrees and the random walk are unchanged by merging parallel edges; the paper's edges (u, v) join two vertices, and the source never uses loops
--   - encoding: the vector identity q^G_T = q^G|_T − L_{T,V\T} L^{-1}_{V\T,V\T} q^G|_{V\T} → the identity at each coordinate v ∈ T; reason: two vectors on T are equal iff they agree at every v ∈ T
--   - encoding: p_u(τ_v < τ_{T\{v}}), a walk probability → a sum of path weights of the walk P(u, w) = c_uw/d_u (hitBefore); reason: the probability of the event, written as a sum over the trajectories that realize it
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Lemma 3.8 and (2), p.12; random walks, p.12; connectivity, p.10

import Mathlib
import Definitions.Def_IncrementalER_scCond
import Definitions.Def_IncrementalER_hitBefore

namespace IncrementalER

/-- **Lemma 3.8** with (2) (excess in a Schur complement, algebraically and by random walks).

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), Lemma 3.8 and (2), p.12; random walk and `τ_S`, p.12; connectivity assumption, p.10.

For a connected graph `G = (V, E, c)` and `T ⊆ V`, for every `v ∈ T`:
1. `q^G_T(v) = q^G(v) − (L_{T,V∖T} L^{−1}_{V∖T,V∖T} q^G|_{V∖T})(v)`;
2. `q^G_T(v) = q^G(v) + ∑_{u ∈ V∖T} q^G(u) p_u(τ_v < τ_{T∖{v}})`.

**Formalization Note.** The vector identity of the lemma is stated coordinatewise at each
`v ∈ T`; `L^{−1}_{V∖T,V∖T}` is `grounded c T`. `p_u(τ_v < τ_{T∖{v}})` is defined from path weights
of the walk `P(u, w) = c_uw/d_u` (`hitBefore`); for `T = {v}` it is the probability of ever
reaching `v`. -/
theorem lemma_3_8 {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ) (hc : IsGraph c)
    (hconn : Connected c) (T : Finset V) (v : V) (hv : v ∈ T) :
    excessT c T v = excess c v -
        ∑ a : {x // x ∉ T}, ∑ b : {x // x ∉ T}, lap c v a * grounded c T a b * excess c b ∧
      excessT c T v = excess c v +
        ∑ u ∈ Finset.univ.filter (· ∉ T), excess c u * hitBefore c u v (T.erase v) := by sorry

end IncrementalER
