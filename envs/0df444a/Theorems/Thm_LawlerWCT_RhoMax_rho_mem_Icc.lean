-- Prove2me | Theorems.Thm_LawlerWCT_RhoMax_rho_mem_Icc
-- name    : LawlerWCT.RhoMax.rho_mem_Icc
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:13.507502+00:00
-- url     : https://prove2.me/theorems/924a3cac-3329-49d1-a959-6648b6936968
-- title:
--   §7, p. 16 — with integer data −w* ≤ w_j ≤ w*, 1 ≤ p_j ≤ p*, every attainable ratio lies in [−w*, w*]
-- statement:
--   Let $N$ be a finite job set whose weights and processing times are integers satisfying
--   $$-w^*\le w_j\le w^*,\qquad 1\le p_j\le p^*\qquad(j\in N).$$
--   Then for every nonempty $I\subseteq N$,
--   $$-w^*\le\rho(I)=\frac{\sum_{j\in I}w_j}{\sum_{j\in I}p_j}\le w^* .$$
--   In particular the optimal ratio, the ratio of a ρ-maximal initial set, lies in the interval $[-w^*,w^*]$, which is the starting interval of the binary search.
--
--   **Formalization Note.** The statement bounds the ratio of every nonempty subset of $N$, not only the optimal one, which is a slight generalisation of the paper's sentence; the precedence digraph plays no role and does not appear. The data are integers cast to reals.
-- source:
--   Lawler, Sequencing jobs to minimize total weighted completion time subject to precedence constraints, IRIA-LABORIA Rapport de Recherche No. 205 (Dec. 1976), HAL hal-04716371v1, p. 16, §7, sentence "Then surely the optimal value of ρ is contained in the interval [− w*, w*]."

import Mathlib
import Definitions.Def_LawlerWCT_RhoMax_Model

namespace LawlerWCT.RhoMax

theorem rho_mem_Icc {ι : Type*} (N : Finset ι) (w p : ι → ℤ) (wstar pstar : ℤ)
    (hw : ∀ j ∈ N, -wstar ≤ w j ∧ w j ≤ wstar) (hpb : ∀ j ∈ N, 1 ≤ p j ∧ p j ≤ pstar) :
    ∀ I ⊆ N, I.Nonempty →
      -(wstar : ℝ) ≤ LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) I ∧
        LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) I ≤ (wstar : ℝ) := by sorry

end LawlerWCT.RhoMax
