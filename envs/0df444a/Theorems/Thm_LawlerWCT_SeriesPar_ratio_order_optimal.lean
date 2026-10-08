-- Prove2me | Theorems.Thm_LawlerWCT_SeriesPar_ratio_order_optimal
-- name    : LawlerWCT.SeriesPar.ratio_order_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:58:39.281179+00:00
-- url     : https://prove2.me/theorems/89e73800-751e-4308-a4ed-eb9283339995
-- title:
--   §5, p. 10 — composite jobs in nonincreasing ratio order give a minimum-cost arrangement
-- statement:
--   Let $p_j>0$ and $w_j$ be the processing times and real weights of the jobs, and let $F=\{c_1,\dots,c_m\}$ be a set of composite jobs: nonempty, pairwise disjoint sequences of distinct jobs. Each composite job $c$ is treated as a single job with weight $\sum_{j\in c}w_j$, processing time $\sum_{j\in c}p_j$ and ratio
--   $$\rho(c)=\frac{\sum_{j\in c}w_j}{\sum_{j\in c}p_j}.$$
--   If $L$ arranges the composite jobs of $F$ in nonincreasing order of ratio and $L'$ arranges them in any order, then the sequence obtained by expanding $L$ costs no more than the one obtained by expanding $L'$:
--   $$\sum_{j}w_jC_j(L)\ \le\ \sum_j w_jC_j(L').$$
--
--   This is Smith's ratio rule applied to composite jobs, the step "an optimal sequence can be found by simply placing them in nonincreasing order of the ratios".
--
--   **Formalization Note** The statement compares arrangements that keep each composite job together, with no precedence constraints between composite jobs; that the precedence constraints have been absorbed into the composite jobs is the content of the other milestones. Sequences of composite jobs are lists of lists, and "expanding" is `List.flatten`.
-- source:
--   Lawler, Sequencing jobs to minimize total weighted completion time subject to precedence constraints, IRIA-LABORIA Rapport de Recherche No. 205 (Dec. 1976), HAL hal-04716371v1, p. 10, §5, sentence "For any such set of jobs, an optimal sequence can be found by simply placing them in nonincreasing order of the ratios"

import Mathlib
import Definitions.Def_LawlerWCT_SeriesPar_Model

namespace LawlerWCT.SeriesPar

theorem ratio_order_optimal {ι : Type*} [DecidableEq ι] (p w : ι → ℝ)
    (F : List (List ι)) (hne : ∀ c ∈ F, c ≠ []) (hnd : F.flatten.Nodup)
    (hp : ∀ j ∈ F.flatten, 0 < p j) :
    ∀ L L' : List (List ι), L.Perm F → IsRatioOrder p w L → L'.Perm F →
      SingleMachinePrec.Biclique.weightedCompletion p w F.flatten.toFinset L.flatten ≤
        SingleMachinePrec.Biclique.weightedCompletion p w F.flatten.toFinset L'.flatten := by sorry

end LawlerWCT.SeriesPar
