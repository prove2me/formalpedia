-- Prove2me | Theorems.Thm_MetricTSPSublinear_cutLP_strong_duality
-- name    : MetricTSPSublinear.cutLP_strong_duality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:39:02.94474+00:00
-- url     : https://prove2.me/theorems/5a45f6f7-fced-5403-a356-328036e2a267
-- title:
--   Strong duality for the cut LP
-- statement:
--   Let $d$ be a metric on $V$ and $S\subseteq V$. There is a feasible dual solution $y$ of the cut LP on $S$ (nonnegative weights on the sets $\emptyset\ne A\subsetneq S$, separating every pair $u\ne v$ of $S$ with total weight at most $d(u,v)$) whose value equals the cut LP value:
--   $$\sum_A y_A=K(S).$$
--
--   Together with weak duality this identifies $K(S)$ with the maximum weight of a dominated Steiner tree on $S$ (Lemma 4.2), which is how the paper reasons about $K$ and $K(S)$ throughout.
--
--   **Formalization Note** The proof reduces to the platform's LP strong duality theorem for standard-form linear programs.
-- source:
--   Azarmehr–Behnezhad 2026, Metric TSP in Sublinear Time: Breaking Two Approximation, https://arxiv.org/abs/2611.04283, §2.1.3 p.4 and §4.1 p.12: the dual LP (D)/(5) of the Cut LP (P) has value K.

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_MetricTSPSublinear_cutLP
import Definitions.Def_MetricTSPSublinear_IsDualFeasible

namespace MetricTSPSublinear

/-- **Strong duality for the cut LP.** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*,
arXiv:2611.04283, §2.1.3, p.4 (PDF p.6), display (D): "K = max { Σ y_A | Σ_{A : e ∈ δ(A)} y_A ≤ w_e (∀e), y ≥ 0 }".
Some feasible dual solution on `S` has value exactly `K(S)`. -/
theorem cutLP_strong_duality {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (S : Finset (Fin n)) :
    ∃ y : Finset (Fin n) → ℝ, IsDualFeasible d S y ∧ ∑ A, y A = cutLP d S := by sorry

end MetricTSPSublinear
