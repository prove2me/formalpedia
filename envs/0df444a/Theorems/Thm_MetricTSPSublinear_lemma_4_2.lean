-- Prove2me | Theorems.Thm_MetricTSPSublinear_lemma_4_2
-- name    : MetricTSPSublinear.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:29:56.329355+00:00
-- url     : https://prove2.me/theorems/6403983c-887d-4c61-b9b8-112dbc9f57d4
-- title:
--   Lemma 4.2 — every feasible dual solution is a dominated Steiner tree of equal weight
-- statement:
--   Let $d$ be a metric on $V$ and $S\subseteq V$ nonempty. For every feasible solution $y$ of the dual LP (5) on $S$ there is a weighted Steiner tree $F$ on $S$ (leaves in $S$, nonnegative weights) that is dominated by the metric and satisfies
--   $$w(F)=\sum_A y_A.$$
--
--   With Claim 4.1 this shows that $K(S)$ is the largest weight of a dominated Steiner tree on $S$.
--
--   Differences from the source:
--   - generalization: the point set V → any nonempty S ⊆ Fin n with the metric induced on S; reason: S = Finset.univ is the page's statement; for general S it is the page's statement for the metric induced on S
--   - encoding: the vertex set V of a metric (nonempty) → S.Nonempty as a hypothesis; reason: a tree has a node, so the statement needs a point
--   - encoding: an n-point metric (V, d) → DoublingMST.IsMetric d on Fin n: d u v = 0 iff u = v, symmetry, triangle inequality; reason: same instances; nonnegativity follows
--   - encoding: a weighted tree F → SteinerTree S (leaves in S, weights ≥ 0), as for Claim 4.1; reason: the page's construction has these properties and its use in Lemma 4.3 needs them
-- source:
--   A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea2397da2e82c8f8baada200e333f32a133395de02943b1fce22946e4a745), https://arxiv.org/abs/2611.04283, §4.1, Lemma 4.2, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_MetricTSPSublinear_IsDualFeasible
import Definitions.Def_MetricTSPSublinear_Dominated

namespace MetricTSPSublinear

/-- **Lemma 4.2.** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283 (held version,
sha256 a86ea239…), §4.1, p.12 (PDF p.14): "For any feasible dual solution y, there exists a weighted tree F
that is dominated by the metric, and satisfies w(F) = ∑_A y_A."

For every metric `d` on `Fin n`, every nonempty point set `S` and every feasible solution `y` of the dual (5) on
`S`, there is a Steiner tree `F` on `S` (node set containing `S`, leaves in `S`, nonnegative weights) that is
dominated by `d` and has weight `w(F) = ∑_A y_A`.

**Formalization Note.** `S = Finset.univ` is the page's statement; a general `S` is the same statement for the
metric induced on `S`. `S` is nonempty because a tree has a node. -/
theorem lemma_4_2 {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (S : Finset (Fin n)) (hS : S.Nonempty)
    (y : Finset (Fin n) → ℝ) (hy : IsDualFeasible d S y) :
    ∃ F : SteinerTree S, Dominated d F ∧ F.weight = ∑ A, y A := by sorry

end MetricTSPSublinear
