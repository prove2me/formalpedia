-- Prove2me | Theorems.Thm_LawlerWCT_RhoMax_case_3
-- name    : LawlerWCT.RhoMax.case_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:40.793978+00:00
-- url     : https://prove2.me/theorems/78eb44be-562e-4e90-88fe-1e9fc830e3fa
-- title:
--   §7, p. 16, Case 3 — if the best nonempty initial set has zero trial weight, ρ is optimal and I is ρ-maximal
-- statement:
--   Let $G=(N,A)$ be an acyclic digraph on a finite job set $N$, with positive processing times $p_j>0$ and real weights $w_j$, and let $\rho$ be a real trial value with trial weights $\bar w_j=w_j-\rho p_j$. Let $I$ be a nonempty initial set of $N$ of maximum trial weight among all nonempty initial sets of $N$. If
--   $$\sum_{j\in I}\bar w_j=0,$$
--   then $\rho(I)=\rho$ and $I$ is a ρ-maximal initial set of $N$:
--   $$\rho(I)\ge\rho(I')\qquad\text{for every nonempty initial set } I' \text{ of } N .$$
--
--   This is the third outcome of a trial value: the trial value equals the optimal ratio, and the maximum-weight initial set found is ρ-maximal.
--
--   **Formalization Note.** As in Case 2, the maximum is over nonempty initial sets: over all initial sets, the empty set would have weight $0$ and could be returned without being ρ-maximal.
-- source:
--   Lawler, Sequencing jobs to minimize total weighted completion time subject to precedence constraints, IRIA-LABORIA Rapport de Recherche No. 205 (Dec. 1976), HAL hal-04716371v1, p. 16, §7, Case 3

import Mathlib
import Definitions.Def_LawlerWCT_RhoMax_Model

namespace LawlerWCT.RhoMax

theorem case_3 {ι : Type*} (N : Finset ι) (G : ι → ι → Prop)
    (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (p w : ι → ℝ) (hp : ∀ j ∈ N, 0 < p j) (ρ : ℝ) (I : Finset ι)
    (hI : LawlerWCT.SeriesPar.IsInitialSet G N I) (hIne : I.Nonempty)
    (hmax : ∀ I', LawlerWCT.SeriesPar.IsInitialSet G N I' → I'.Nonempty → trialWeight p w ρ I' ≤ trialWeight p w ρ I)
    (hzero : trialWeight p w ρ I = 0) :
    LawlerWCT.SeriesPar.IsRhoMaximal G p w N I ∧ LawlerWCT.SeriesPar.rho p w I = ρ := by sorry

end LawlerWCT.RhoMax
