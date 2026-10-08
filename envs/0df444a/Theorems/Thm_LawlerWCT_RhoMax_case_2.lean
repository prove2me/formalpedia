-- Prove2me | Theorems.Thm_LawlerWCT_RhoMax_case_2
-- name    : LawlerWCT.RhoMax.case_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:52.776955+00:00
-- url     : https://prove2.me/theorems/75a7b202-c266-42c6-8503-0744186c6098
-- title:
--   §7, p. 15, Case 2 — if the best nonempty initial set has negative trial weight, ρ exceeds every attainable ratio
-- statement:
--   Let $G=(N,A)$ be an acyclic digraph on a finite job set $N$, with positive processing times $p_j>0$ and real weights $w_j$, and let $\rho$ be a real trial value with trial weights $\bar w_j=w_j-\rho p_j$. Let $I$ be a nonempty initial set of $N$ of maximum trial weight among all nonempty initial sets of $N$. If
--   $$\sum_{j\in I}\bar w_j<0,$$
--   then the trial value is too large:
--   $$\rho(I')<\rho\qquad\text{for every nonempty initial set } I' \text{ of } N .$$
--
--   This is the second outcome of a trial value in the binary search: the optimal ratio lies strictly below $\rho$.
--
--   **Formalization Note.** The maximum is taken over **nonempty** initial sets. Over all initial sets the empty set has weight $0$, so a maximum-weight initial set never has negative weight and Case 2 could not occur; the nonempty reading is the one under which the case is meaningful. $\rho(\emptyset)$ is $0$ in Lean, so the conclusion also ranges over nonempty sets only.
-- source:
--   Lawler, Sequencing jobs to minimize total weighted completion time subject to precedence constraints, IRIA-LABORIA Rapport de Recherche No. 205 (Dec. 1976), HAL hal-04716371v1, p. 15, §7, Case 2

import Mathlib
import Definitions.Def_LawlerWCT_RhoMax_Model

namespace LawlerWCT.RhoMax

theorem case_2 {ι : Type*} (N : Finset ι) (G : ι → ι → Prop)
    (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (p w : ι → ℝ) (hp : ∀ j ∈ N, 0 < p j) (ρ : ℝ) (I : Finset ι)
    (hI : LawlerWCT.SeriesPar.IsInitialSet G N I) (hIne : I.Nonempty)
    (hmax : ∀ I', LawlerWCT.SeriesPar.IsInitialSet G N I' → I'.Nonempty → trialWeight p w ρ I' ≤ trialWeight p w ρ I)
    (hneg : trialWeight p w ρ I < 0) :
    ∀ I', LawlerWCT.SeriesPar.IsInitialSet G N I' → I'.Nonempty → LawlerWCT.SeriesPar.rho p w I' < ρ := by sorry

end LawlerWCT.RhoMax
