-- Prove2me | Theorems.Thm_IncrementalER_lemma_5_2
-- name    : IncrementalER.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:08:38.94035+00:00
-- url     : https://prove2.me/theorems/1c7fb9a9-4e23-4adc-9582-a1af42d709c5
-- title:
--   Lemma 5.2, p.29 — the grounded inverse $K=L^{-1}_{\bar S,\bar S}$ and random walks
-- statement:
--   Let $G$ be a connected graph, $S\subseteq V$ nonempty, $\bar S=V\setminus S$, and $K=L^{-1}_{\bar S,\bar S}$. Then:
--
--   1. $K_{vv}=R_{\mathrm{eff}}(v,S)$ for every $v\in\bar S$, where $R_{\mathrm{eff}}(v,S)$ is the minimum electrical energy of a unit flow from $v$ to the set $S$;
--   2. $K_{uv}/K_{vv}=p_u(\tau_v<\tau_S)$ for all $u,v\in\bar S$;
--   3. $1/(K_{vv}d_v)=p_v(\tau_S<\tau_{v+})$ for every $v\in\bar S$;
--   4. $K_{vu}=\mathbb E_v[N_u(\tau_S)]/d_u$ for all $u,v\in\bar S$, where $N_u(\tau_S)$ is the number of visits to $u$ before the walk reaches $S$.
--
--   These identities turn the paper's leverage-degree formula into quantities a random walk can sample. Connectivity is the paper's standing assumption ("We assume throughout that everywhere we are dealing exclusively with connected graphs", p.10) and is a hypothesis.
--
--   Differences from the source:
--   - encoding: G = (V, E, c) an undirected capacitated multigraph (p.10) → a symmetric nonnegative conductance function with zero diagonal (parallel capacities added, no loops); reason: the Laplacian, effective resistances, leverage degrees and the random walk are unchanged by merging parallel edges; the paper's edges (u, v) join two vertices, and the source never uses loops
--   - encoding: S ⊆ V → S nonempty; reason: for S = ∅ the grounded Laplacian is L itself, which is singular, so K is undefined; the hypothesis excludes only that case
--   - encoding: probabilities and expectations of the walk → sums of path weights of the walk P(x, y) = c_xy/d_x; reason: the probability of each event written as a sum over the trajectories that realize it
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Lemma 5.2 and footnote 7, p.29; τ_{v+} and N_u(τ_S), p.29; connectivity, p.10

import Mathlib
import Definitions.Def_IncrementalER_scCond
import Definitions.Def_IncrementalER_hitBefore

namespace IncrementalER

/-- **Lemma 5.2** (grounded Laplacian inverse and random walks).

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), Lemma 5.2 and footnote 7,
p.29; `τ_{v+}` and `N_u(τ_S)`, p.29; connectivity assumption, p.10.

Let `G` be a connected graph, `S ⊆ V` nonempty and `K = L^{−1}_{S̄,S̄}`. Then
1. `K_vv = Reff(v, S)` for every `v ∈ S̄`;
2. `K_uv / K_vv = p_u(τ_v < τ_S)` for every `u, v ∈ S̄`;
3. `1/(K_vv d_v) = p_v(τ_S < τ_{v+})` for every `v ∈ S̄`;
4. `K_vu = E_v[N_u(τ_S)] / d_u` for every `u, v ∈ S̄`.

**Formalization Note.** `Reff(v, S)` is the minimum energy of a unit flow from `v` to `S`
(footnote 7), not `K_vv`; every probability and expectation is a sum of path weights of the walk
`P(x, y) = c_xy/d_x`. `S ≠ ∅` makes `L_{S̄,S̄}` invertible (for `S = ∅` the grounded Laplacian is the
singular `L`). -/
theorem lemma_5_2 {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ) (hc : IsGraph c)
    (hconn : Connected c) (S : Finset V) (hS : S.Nonempty) :
    (∀ v : {x // x ∉ S}, grounded c S v v = reffSet c v S) ∧
      (∀ u v : {x // x ∉ S}, grounded c S u v / grounded c S v v = hitBefore c u v S) ∧
      (∀ v : {x // x ∉ S}, 1 / (grounded c S v v * capDeg c v) = escapeProb c v S) ∧
      (∀ u v : {x // x ∉ S}, grounded c S v u = expVisits c v S u / capDeg c u) := by sorry

end IncrementalER
