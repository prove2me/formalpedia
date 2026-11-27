-- Prove2me | Theorems.Thm_MetricTSPSublinear_cutLP_weak_duality
-- name    : MetricTSPSublinear.cutLP_weak_duality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:39:00.818738+00:00
-- url     : https://prove2.me/theorems/310fb464-a148-5b90-9b22-79a2150a958c
-- title:
--   Weak duality for the cut LP
-- statement:
--   Let $d$ be a metric on $V$ and $S\subseteq V$. A **feasible dual solution** of the cut LP on $S$ assigns $y_A\ge0$ to the sets $\emptyset\ne A\subsetneq S$ (and $0$ to all other sets) so that every pair $u\ne v$ in $S$ is separated with total weight at most its distance:
--   $$\sum_{A:\ |A\cap\{u,v\}|=1}y_A\le d(u,v).$$
--   Then
--   $$\sum_A y_A\le K(S),$$
--   where $K(S)$ is the value of the cut LP of the metric induced on $S$.
--
--   This is the inequality through which every dominated Steiner tree, and in particular the solution $F_{\mathrm{dual}}$ built by the sublinear algorithm, certifies a lower bound on $K$.
-- source:
--   Azarmehr–Behnezhad 2026, Metric TSP in Sublinear Time: Breaking Two Approximation, https://arxiv.org/abs/2611.04283, §2.1.3 p.4 and §4.1 p.12: the dual LP (D)/(5) of the Cut LP (P) has value K.

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_MetricTSPSublinear_cutLP
import Definitions.Def_MetricTSPSublinear_IsDualFeasible

namespace MetricTSPSublinear

/-- **Weak duality for the cut LP.** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*,
arXiv:2611.04283, §4.1, p.12 (PDF p.14), display (5): the dual of (P) is `max Σ_A y_A` subject to
`Σ_{A : e ∈ δ(A)} y_A ≤ w_e`, `y ≥ 0`. Every feasible dual solution on `S` has value at most `K(S)`. -/
theorem cutLP_weak_duality {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (S : Finset (Fin n)) (y : Finset (Fin n) → ℝ) (hy : IsDualFeasible d S y) :
    ∑ A, y A ≤ cutLP d S := by sorry

end MetricTSPSublinear
