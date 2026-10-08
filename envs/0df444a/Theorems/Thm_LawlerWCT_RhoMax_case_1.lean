-- Prove2me | Theorems.Thm_LawlerWCT_RhoMax_case_1
-- name    : LawlerWCT.RhoMax.case_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:54.06385+00:00
-- url     : https://prove2.me/theorems/e9729d48-3af2-4765-ae7e-309bbbf55da7
-- title:
--   §7, p. 15, Case 1 — a set of positive trial weight Σ(w_j − ρp_j) > 0 has ratio ρ(I) > ρ
-- statement:
--   Let $N$ be a finite job set with positive processing times $p_j>0$ and real weights $w_j$, let $\rho$ be a real trial value, and let $I\subseteq N$. If the weight of $I$ with respect to the trial weights $\bar w_j=w_j-\rho p_j$ is strictly positive,
--   $$\sum_{j\in I}\bar w_j=\sum_{j\in I}w_j-\rho\sum_{j\in I}p_j>0,$$
--   then $I$ is nonempty and
--   $$\rho(I)=\frac{\sum_{j\in I}w_j}{\sum_{j\in I}p_j}>\rho .$$
--
--   This is the first of the three outcomes of testing a trial value $\rho$ in the binary search for the optimal ratio: the trial value is too small, and $I$ itself has a larger ratio.
--
--   **Formalization Note.** The statement does not need $I$ to be an initial set, nor the precedence digraph; it holds for every $I\subseteq N$, which is slightly stronger than the paper's use of it for a maximum-weight initial set. The printed display omits the bar over the left-hand $w_j$; the left-hand side is the weight of $I$ with respect to $\bar w_j$, as the sentence before it says.
-- source:
--   Lawler, Sequencing jobs to minimize total weighted completion time subject to precedence constraints, IRIA-LABORIA Rapport de Recherche No. 205 (Dec. 1976), HAL hal-04716371v1, p. 15, §7, Case 1

import Mathlib
import Definitions.Def_LawlerWCT_RhoMax_Model

namespace LawlerWCT.RhoMax

theorem case_1 {ι : Type*} (N : Finset ι) (p w : ι → ℝ) (hp : ∀ j ∈ N, 0 < p j)
    (ρ : ℝ) (I : Finset ι) (hIN : I ⊆ N) (hpos : 0 < trialWeight p w ρ I) :
    I.Nonempty ∧ ρ < LawlerWCT.SeriesPar.rho p w I := by sorry

end LawlerWCT.RhoMax
