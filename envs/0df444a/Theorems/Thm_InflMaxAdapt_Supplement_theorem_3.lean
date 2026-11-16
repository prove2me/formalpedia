-- Prove2me | Theorems.Thm_InflMaxAdapt_Supplement_theorem_3
-- name    : InflMaxAdapt.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:44:34.370076+00:00
-- url     : https://prove2.me/theorems/4cbefb1b-ad67-4ed7-992f-829cceabf609
-- title:
--   Theorem 3 — on bi-directed forests, $\mathrm{Adaptive}_k \le 2\,\mathrm{Static}_k$
-- statement:
--   Let $(V, \mathbf p)$ be a bi-directed forest instance of influence maximization: $V$ is finite, $\mathbf p \in [0,1]^{V^2}$, every arc is live independently, and the undirected graph on $V$ with an edge $\{u,v\}$ for each pair of distinct vertices with $p_{u,v} > 0$ or $p_{v,u} > 0$ is a forest (opposite arcs may have different probabilities). Then for every budget $k \in \mathbb N$,
--   $$
--   \mathrm{Adaptive}_k(V, \mathbf p) \;\le\; 2\,\mathrm{Static}_k(V, \mathbf p),
--   $$
--   where $\mathrm{Adaptive}_k$ is the optimum over all adaptive policies with budget $k$, full-adoption feedback and external randomness, and $\mathrm{Static}_k$ the optimum over seed sets of size at most $k$.
--
--   The bound covers every orientation of a forest (in- and out-arborescences) and every undirected forest, and is the first constant bound for undirected forests.
--
--   Differences from the source:
--   - encoding: p ∈ [0,1]^{V²} as part of an instance → hypothesis ∀ u v, 0 ≤ p u v ∧ p u v ≤ 1 on p : V → V → ℝ, loops (v, v) included as in V²; reason: same instances
--   - encoding: Adaptive_k = max over π ∈ Π_k → the published InflMaxAdapt.Adaptive: sSup of the values of all policies with measurable decision rules on probability spaces (Ω : Type, μ); reason: the value set is bounded by |V|; a bound on the sSup is a bound on every policy value, as in the published Theorem 1
--   - encoding: the undirected graph with an edge {u, v} for each pair of distinct vertices with p_{u,v} > 0 or p_{v,u} > 0 is a forest → IsBidirForest p := (SimpleGraph.fromRel (fun u v => 0 < p u v ∨ 0 < p v u)).IsAcyclic; reason: fromRel keeps exactly the pairs u ≠ v with the relation in either direction; same instances
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Theorem 3, printed p.3 (PDF p.4); bi-directed forest defined in Section 4, printed p.11 (PDF p.12); proof printed pp.11–12 (PDF pp.12–13)

import Mathlib
import Definitions.Def_InflMaxAdapt_Static
import Definitions.Def_InflMaxAdapt_Adaptive
import Definitions.Def_InflMaxAdapt_Supplement_IsBidirForest

open MeasureTheory

namespace InflMaxAdapt.Supplement

open InflMaxAdapt

/-- Theorem 3 (bi-directed forests; printed p.3 = PDF p.4, proof in Section 4, printed pp.11–12 =
PDF pp.12–13, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and
Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)): for every bi-directed forest
instance of influence maximization (`p ∈ [0,1]^{V²}` whose support graph
`{ {u, v} : u ≠ v, p_{u,v} > 0 ∨ p_{v,u} > 0 }` is a forest; opposite arcs independent, possibly
with different probabilities) and every budget `k ∈ ℕ`, `Adaptive_k ≤ 2 · Static_k`. -/
theorem theorem_3 {V : Type} [Fintype V] [DecidableEq V] (p : V → V → ℝ)
    (hp : ∀ u v, 0 ≤ p u v ∧ p u v ≤ 1) (hF : IsBidirForest p) (k : ℕ) :
    Adaptive p k ≤ 2 * Static p k := by sorry

end InflMaxAdapt.Supplement
