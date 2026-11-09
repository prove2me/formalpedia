-- Prove2me | Theorems.Thm_LocalPush_pagerank_properties
-- name    : LocalPush.pagerank_properties
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:05:58.604312+00:00
-- url     : https://prove2.me/theorems/8615582a-b6a2-4e05-875a-815c049b0c86
-- title:
--   §4 — PageRank is nonnegative, sums to one, and $d(u)\,\mathrm{pr}_\alpha(u,v)=d(v)\,\mathrm{pr}_\alpha(v,u)$ (4)
-- statement:
--   Let $G$ be a finite simple undirected graph without isolated nodes and $\alpha\in(0,1)$. Then for all $u,v\in V$:
--
--   1. $\mathrm{pr}_\alpha(u,v)\ge0$;
--   2. $\sum_{v\in V}\mathrm{pr}_\alpha(u,v)=1$;
--   3. the symmetry identity
--   $$d(u)\,\mathrm{pr}_\alpha(u,v)=d(v)\,\mathrm{pr}_\alpha(v,u).\tag{4}$$
--
--   The symmetry identity, a consequence of the reversibility of random walks on undirected graphs, is what makes the increments of the active-set process orthogonal (Lemma 5.5).
--
--   Differences from the source:
--   - encoding: pr_α(s) defined as the unique solution of (1) → pr G α σ := α(I − (1 − α)AD⁻¹)⁻¹σ, with D⁻¹ the diagonal of reciprocal degrees; reason: for α ∈ (0, 1) and no isolated nodes the matrix is invertible and this is the unique solution (milestone LocalPush.eq_1_unique); D⁻¹ is the diagonal of reciprocal degrees when degrees are positive
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §4, Properties of PageRank and eq. (4), p.15 (PDF p.15)

import Mathlib
import Definitions.Def_LocalPush_PageRank

open Finset Matrix

namespace LocalPush

/-- **§4, properties of PageRank and the symmetry identity (4).**

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), §4, p.15 (PDF p.15).

"For every u ∈ V, the PageRank values satisfy pr_α(u, v) ≥ 0 for all v ∈ V and ∑_{v∈V} pr_α(u, v) = 1." —
"On undirected graphs, they also satisfy the following symmetry identity […]: d(u) pr_α(u, v) = d(v) pr_α(v, u),
∀ u, v ∈ V. (4)"

For a simple graph without isolated nodes and `α ∈ (0, 1)`, with `pr_α(u, v) = pr G α (e u) v`: every entry is
nonnegative, every row sums to `1`, and `d(u) pr_α(u, v) = d(v) pr_α(v, u)`. -/
theorem pagerank_properties {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : NoIsolated G) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ u v, 0 ≤ pr G α (e u) v) ∧ (∀ u, ∑ v, pr G α (e u) v = 1) ∧
      ∀ u v, deg G u * pr G α (e u) v = deg G v * pr G α (e v) u := by sorry

end LocalPush
