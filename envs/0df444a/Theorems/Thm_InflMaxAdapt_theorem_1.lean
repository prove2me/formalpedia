-- Prove2me | Theorems.Thm_InflMaxAdapt_theorem_1
-- name    : InflMaxAdapt.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:37:39.847797+00:00
-- url     : https://prove2.me/theorems/7968ca2f-6e06-4c21-8fd4-6789a59407c3
-- title:
--   Theorem 1 — on undirected instances, $\mathrm{Adaptive}_k \le 5\sqrt{k}\,\mathrm{Static}_k$
-- statement:
--   Let $(V, \mathbf p)$ be an undirected instance of influence maximization: $V$ is a finite set, $\mathbf p \in [0,1]^{V^2}$ with $p_{u,v} = p_{v,u}$ for all $u, v$, and every arc is live independently. Then for every budget $k \in \mathbb N$,
--   $$
--   \mathrm{Adaptive}_k(V, \mathbf p) \;\le\; 5\sqrt{k}\;\mathrm{Static}_k(V, \mathbf p),
--   $$
--   where $\mathrm{Adaptive}_k$ is the optimum over all adaptive policies with full-adoption feedback and external randomness, and $\mathrm{Static}_k$ is the optimum over seed sets of size at most $k$.
--
--   The adaptivity gap of every undirected instance is therefore at most $5\sqrt k$, independently of the graph; before this result only the linear bound $k$ was known in this generality.
--
--   Differences from the source:
--   - encoding: p ∈ [0,1]^{V²} as part of an instance → hypothesis ∀ u v, 0 ≤ p u v ∧ p u v ≤ 1; loops (v, v) included in V × V as in V²; reason: same instances
--   - encoding: Adaptive_k = max over π ∈ Π_k → sSup of the values of all policies with measurable decision rules on probability spaces (Ω : Type, μ); reason: the value set is bounded by |V|; the bounds stated are equivalent to bounds on every policy's value
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Theorem 1, printed p.3 (PDF p.4)

import Mathlib
import Definitions.Def_InflMaxAdapt_Static
import Definitions.Def_InflMaxAdapt_Adaptive
import Definitions.Def_InflMaxAdapt_IsUndirected

open MeasureTheory

namespace InflMaxAdapt

/-- Theorem 1 (undirected graphs; printed p.3 = PDF p.4, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)): for every undirected instance
of influence maximization (`p ∈ [0,1]^{V²}` with `p_{u,v} = p_{v,u}`, arcs live independently) and
every budget `k ∈ ℕ`, `Adaptive_k ≤ 5 √k · Static_k`, where `Adaptive_k` is the optimum over all
adaptive policies with full-adoption feedback and external randomness. -/
theorem theorem_1 {V : Type} [Fintype V] [DecidableEq V] (p : V → V → ℝ)
    (hp : ∀ u v, 0 ≤ p u v ∧ p u v ≤ 1) (hsym : IsUndirected p) (k : ℕ) :
    Adaptive p k ≤ 5 * Real.sqrt k * Static p k := by sorry

end InflMaxAdapt
