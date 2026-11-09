-- Prove2me | Theorems.Thm_MetricTSPSublinear_claim_4_1
-- name    : MetricTSPSublinear.claim_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:29:06.737206+00:00
-- url     : https://prove2.me/theorems/9f7ba7fc-ddbf-4258-aa82-28a33d1916d2
-- title:
--   Claim 4.1 — the dual solution of a tree is feasible iff the tree is dominated
-- statement:
--   Let $d$ be a metric on $V$, $S\subseteq V$, $F$ a weighted Steiner tree on $S$ and $y$ its dual solution (each edge $e$ of $F$ contributes $w_F(e)$ to $y_A$, $A$ the points on one side of $e$). Then
--   $$y\ \text{is feasible for the dual LP (5) on } S\quad\Longleftrightarrow\quad d_F(u,v)\le d(u,v)\ \text{for all } u,v\in S.$$
--
--   This identifies the dual of the cut LP with dominated Steiner trees: the dual value of $F$ is its weight.
--
--   Differences from the source:
--   - generalization: the point set V → any S ⊆ Fin n with the metric induced on S; reason: S = Finset.univ is the page's statement; for general S it is the page's statement for the metric induced on S, which the paper uses for K(S)
--   - reading: A = the points in one of the two components of F ∖ e → the component not containing the node of a parameter x₀ ∈ S; reason: the page leaves the side open; δ(A) = δ(S ∖ A), so feasibility is the same for either side
--   - encoding: an n-point metric (V, d) → DoublingMST.IsMetric d on Fin n: d u v = 0 iff u = v, symmetry, triangle inequality; reason: same instances; nonnegativity follows
--   - encoding: a weighted Steiner tree whose vertex set contains V and whose leaves are in V → SteinerTree S: nodes Fin m, embedding injective on S, a TreeCoverLB.WeightedTree (tree, weights ≥ 0 on edges), every node with ≤ 1 neighbour a point of S; reason: the same trees
-- source:
--   A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea2397da2e82c8f8baada200e333f32a133395de02943b1fce22946e4a745), https://arxiv.org/abs/2611.04283, §4.1, Claim 4.1, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_MetricTSPSublinear_IsDualFeasible
import Definitions.Def_MetricTSPSublinear_Dominated
import Definitions.Def_MetricTSPSublinear_dualOf

namespace MetricTSPSublinear

/-- **Claim 4.1.** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283 (held version,
sha256 a86ea239…), §4.1, p.12 (PDF p.14): "The corresponding dual solution y of a tree F satisfies the dual
constraints if and only if the tree is dominated by the metric."

For every metric `d` on `Fin n`, every point set `S`, every Steiner tree `F` on `S` and every `x₀ ∈ S`: the dual
solution `dualOf F x₀` of `F` is a feasible solution of the dual (5) on `S` if and only if `F` is dominated by `d`.

**Formalization Note.** `S = Finset.univ` is the page's statement; a general `S` is the same statement for the
metric induced on `S`. `x₀` fixes the side of each edge's cut (see `dualOf`). -/
theorem claim_4_1 {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (S : Finset (Fin n)) (F : SteinerTree S)
    (x₀ : Fin n) (hx₀ : x₀ ∈ S) :
    IsDualFeasible d S (dualOf F x₀) ↔ Dominated d F := by sorry

end MetricTSPSublinear
