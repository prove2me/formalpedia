-- Prove2me | Theorems.Thm_MetricTSPSublinear_claim_6_1
-- name    : MetricTSPSublinear.claim_6_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:54:32.436553+00:00
-- url     : https://prove2.me/theorems/9c97828b-96d2-527f-9787-0809ea5ecbd3
-- title:
--   Claim 6.1: local cell solutions glue to a lower bound on $K$
-- statement:
--   Let $d$ be a metric on $V=\{0,\dots,n-1\}$ and let $K$ be a finite weighted tree (the core, subdivided at all relevant points) with a map $q:V\to V(K)$ that is non-expansive: $d_K(q_u,q_v)\le d(u,v)$. Suppose the edges of $K$ are partitioned among cells $P$, each a connected set of nodes containing at least one edge, every leaf of $K$ is the image $q_s$ of some point, and every point $v$ is assigned to a cell $P(v)$ containing $q_v$. The **ports** $\partial P$ of a cell are its nodes shared with other cells. For each cell $P$ let $t_P$ be a weighted tree whose nodes include the points of $V_P=\{v:P(v)=P\}$ and the ports of $P$, whose leaves are such points or ports, and which satisfies the cell distance constraints
--   $$d_{t_P}(u,v)\le d(u,v)\ (u,v\in V_P),\qquad d_{t_P}(v,p)\le d_K(q_v,p)\ (v\in V_P,\ p\in\partial P),\qquad d_{t_P}(p,p')\le d_K(p,p')\ (p,p'\in\partial P).$$
--   Then the local solutions glue to a feasible dual solution of the cut LP, and in particular
--   $$\sum_P w(t_P)\le K,$$
--   where $K$ on the right is the cut LP value of $V$.
--
--   This is the step that makes the weight $L=w(F_{\mathrm{dual}})$ estimated by the sublinear algorithm a valid lower bound on the cut LP value.
--
--   **Formalization Note** The paper's continuous core $R(C)$ is replaced by a finite subdivision; the dual of the glued tree is built cell by cell, using the projection of a node onto a cell, and weak duality concludes.
-- source:
--   Azarmehr–Behnezhad 2026, Metric TSP in Sublinear Time: Breaking Two Approximation, https://arxiv.org/abs/2611.04283, §6, Claim 6.1 and constraints (9), pp.21–22 (PDF pp.23–24).

import Mathlib
import Definitions.Def_TreeCoverLB_WeightedTree
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_MetricTSPSublinear_cutLP
import Definitions.Def_MetricTSPSublinear_IsPort

open scoped Classical

namespace MetricTSPSublinear

/-- **Claim 6.1 (discrete form).** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*,
arXiv:2611.04283, §6, p.21–22 (PDF p.23–24): "Given local solutions t_P for each cell P satisfying (9), we can combine
them to obtain a global solution F, which is a Steiner tree spanning V and dominated by the metric." Consequently
`Σ_P w(t_P) ≤ K`.

The core is a finite weighted tree `K` (a subdivision of `R(C)` containing all mapped points and ports), `q` is a
non-expansive map of the points into it (Lemma 5.3), the cells are connected node sets partitioning the edges of `K`,
`cell v` is the cell of `v` (with `q v` in it), and each cell `P` carries a weighted tree `t P` with embeddings of its
vertices (`ev P`) and ports (`ep P`) satisfying the three constraints (9) with `d_C = K.dist`; leaves of `t P` are
vertices or ports of `P`, and leaves of `K` are images of points.

**Formalization Note.** Instead of gluing explicitly, the proof builds the dual solution of the glued tree and applies
weak duality. Cells are required to contain at least one edge of `K` (positive length). -/
theorem claim_6_1 {n m : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (K : TreeCoverLB.WeightedTree (Fin m)) (q : Fin n → Fin m) (hq : ∀ u v, K.dist (q u) (q v) ≤ d u v)
    {ι : Type*} [Fintype ι] (cellNodes : ι → Finset (Fin m))
    (hconn : ∀ P, (K.G.induce (cellNodes P : Set (Fin m))).Preconnected)
    (hedge : ∀ a b, K.G.Adj a b → ∃! P, a ∈ cellNodes P ∧ b ∈ cellNodes P)
    (hcellEdge : ∀ P, ∃ a b, K.G.Adj a b ∧ a ∈ cellNodes P ∧ b ∈ cellNodes P)
    (cell : Fin n → ι) (hcell : ∀ v, q v ∈ cellNodes (cell v))
    (hleafK : ∀ c, (∀ y₁ y₂, K.G.Adj c y₁ → K.G.Adj c y₂ → y₁ = y₂) → ∃ s, q s = c)
    (mm : ι → ℕ) (t : ∀ P, TreeCoverLB.WeightedTree (Fin (mm P)))
    (ev : ∀ P, Fin n → Fin (mm P)) (ep : ∀ P, Fin m → Fin (mm P))
    (h9a : ∀ P u v, cell u = P → cell v = P → (t P).dist (ev P u) (ev P v) ≤ d u v)
    (h9b : ∀ P v p, cell v = P → MetricTSPSublinear.IsPort cellNodes P p →
      (t P).dist (ev P v) (ep P p) ≤ K.dist (q v) p)
    (h9c : ∀ P p p', MetricTSPSublinear.IsPort cellNodes P p → MetricTSPSublinear.IsPort cellNodes P p' →
      (t P).dist (ep P p) (ep P p') ≤ K.dist p p')
    (hleafT : ∀ P c, (∀ y₁ y₂, (t P).G.Adj c y₁ → (t P).G.Adj c y₂ → y₁ = y₂) →
      (∃ v, cell v = P ∧ ev P v = c) ∨ (∃ p, MetricTSPSublinear.IsPort cellNodes P p ∧ ep P p = c)) :
    ∑ P, ∑ e ∈ (t P).G.edgeFinset, (t P).w e ≤ cutLP d Finset.univ := by sorry

end MetricTSPSublinear
