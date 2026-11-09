-- Prove2me | Theorems.Thm_InflMaxAdapt_footnote_3
-- name    : InflMaxAdapt.footnote_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:38:09.228133+00:00
-- url     : https://prove2.me/theorems/b4fb4395-4e1d-48e4-bff0-a9b8092fbea3
-- title:
--   Footnote 3 — $\mathrm{Static}_k$ and $\mathrm{Adaptive}_k$ agree in the arc and undirected-edge representations
-- statement:
--   Let $(V, \mathbf p)$ be an undirected instance: $\mathbf p \in [0,1]^{V^2}$ with $p_{u,v} = p_{v,u}$, every arc live independently. Let $q_{\{u,v\}} = p_{u,v}$ and consider the **undirected-edge representation**, in which every pair $\{u,v\}$ is a single edge live independently with probability $q_{\{u,v\}}$ and cascades are connected components through the seeds. Then for every budget $k \in \mathbb N$,
--   $$
--   \mathrm{Static}_k(V, \mathbf p) = \mathrm{Static}_k^{\mathrm{edge}}(V, q)
--   \quad\text{and}\quad
--   \mathrm{Adaptive}_k(V, \mathbf p) = \mathrm{Adaptive}_k^{\mathrm{edge}}(V, q),
--   $$
--   where both adaptive values are over policies with full-adoption feedback in their own representation.
--
--   This is what allows the proof of Theorem 1 to work with independent undirected edges and connection events $u \leftrightarrow v$ instead of directed reachability.
--
--   Differences from the source:
--   - encoding: p ∈ [0,1]^{V²} as part of an instance → hypothesis ∀ u v, 0 ≤ p u v ∧ p u v ≤ 1; loops (v, v) included in V × V as in V²; reason: same instances
--   - encoding: live undirected edges on unordered pairs {u, v} → live edge set a Finset (Sym2 V) whose potential edges include the diagonal pairs s(v, v); reason: diagonal pairs never affect connectivity; same connection events
--   - encoding: Adaptive_k = max over π ∈ Π_k → sSup of the values of all policies with measurable decision rules on probability spaces (Ω : Type, μ); reason: the value set is bounded by |V|; the bounds stated are equivalent to bounds on every policy's value
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Section 2, footnote 3, printed p.5 (PDF p.6)

import Mathlib
import Definitions.Def_InflMaxAdapt_Static
import Definitions.Def_InflMaxAdapt_Adaptive
import Definitions.Def_InflMaxAdapt_edgeStatic
import Definitions.Def_InflMaxAdapt_edgeAdaptive
import Definitions.Def_InflMaxAdapt_symmToEdge

open MeasureTheory

namespace InflMaxAdapt

/-- Footnote 3 (printed p.5 = PDF p.6, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)): on an undirected instance (`p_{u,v} = p_{v,u}`,
the two arcs of a pair independent), replacing each pair `{u, v}` by one independent undirected
edge live with probability `p_{u,v}` changes neither `Static_k` nor `Adaptive_k` (for adaptive
policies with full-adoption feedback), for every budget `k`. -/
theorem footnote_3 {V : Type} [Fintype V] [DecidableEq V] (p : V → V → ℝ)
    (hp : ∀ u v, 0 ≤ p u v ∧ p u v ≤ 1) (h : IsUndirected p) (k : ℕ) :
    Static p k = edgeStatic (symmToEdge p h) k ∧ Adaptive p k = edgeAdaptive (symmToEdge p h) k := by sorry

end InflMaxAdapt
