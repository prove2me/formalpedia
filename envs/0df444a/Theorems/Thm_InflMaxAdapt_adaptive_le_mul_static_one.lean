-- Prove2me | Theorems.Thm_InflMaxAdapt_adaptive_le_mul_static_one
-- name    : InflMaxAdapt.adaptive_le_mul_static_one
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:37:35.55182+00:00
-- url     : https://prove2.me/theorems/05225efa-1ba9-4904-8d9c-fe0bfef9abc6
-- title:
--   Section 1.1 — $\mathrm{Adaptive}_k \le k\,\mathrm{Static}_1$
-- statement:
--   For every instance $(V, \mathbf p)$ of influence maximization (not necessarily undirected) and every budget $k \in \mathbb N$,
--   $$
--   \mathrm{Adaptive}_k(V, \mathbf p) \;\le\; k \cdot \mathrm{Static}_1(V, \mathbf p).
--   $$
--   This is the elementary linear bound on the adaptivity gap, which follows from adaptive submodularity of influence under full-adoption feedback. The proof of Theorem 1 uses it for budgets $k \le 3$.
--
--   Differences from the source:
--   - encoding: p ∈ [0,1]^{V²} as part of an instance → hypothesis ∀ u v, 0 ≤ p u v ∧ p u v ≤ 1; loops (v, v) included in V × V as in V²; reason: same instances
--   - encoding: Adaptive_k = max over π ∈ Π_k → sSup of the values of all policies with measurable decision rules on probability spaces (Ω : Type, μ); reason: the value set is bounded by |V|; the bounds stated are equivalent to bounds on every policy's value
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Section 1.1, printed p.2 (PDF p.3)

import Mathlib
import Definitions.Def_InflMaxAdapt_Static
import Definitions.Def_InflMaxAdapt_Adaptive

open MeasureTheory

namespace InflMaxAdapt

/-- `Adaptive_k ≤ k · Static_1` (Section 1.1, printed p.2 = PDF p.3, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)), the elementary
bound from adaptive submodularity: for every instance `(V, p)` (directed, no symmetry assumed) and
every budget `k`. -/
theorem adaptive_le_mul_static_one {V : Type} [Fintype V] [DecidableEq V] (p : V → V → ℝ)
    (hp : ∀ u v, 0 ≤ p u v ∧ p u v ≤ 1) (k : ℕ) :
    Adaptive p k ≤ k * Static p 1 := by sorry

end InflMaxAdapt
