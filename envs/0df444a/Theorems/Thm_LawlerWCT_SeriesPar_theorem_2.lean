-- Prove2me | Theorems.Thm_LawlerWCT_SeriesPar_theorem_2
-- name    : LawlerWCT.SeriesPar.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:57:05.845996+00:00
-- url     : https://prove2.me/theorems/8336c5ec-b0ce-45c5-bf17-2416976025b3
-- title:
--   Theorem 2, p. 8 — some optimal sequence runs a ρ-maximal initial set of a module consecutively, before the rest of the module
-- statement:
--   Throughout, $N$ is a finite set of jobs to be sequenced on a single machine, $G=(N,A)$ is an acyclic digraph on $N$ (job $i$ must precede job $j$ when there is a directed path from $i$ to $j$), job $j$ has a processing time $p_j>0$ and a real weight $w_j$, and the cost of a feasible sequence is $\sum_{j} w_j C_j$, where $C_j$ is the completion time of $j$ when the machine starts at time $0$ and never idles.
--
--   Let $M$ be a job module of $G$ and let $I$ be a $\rho$-maximal initial set of $M$ (Definition 3). Then there is an optimal sequence $\tau$ for $N$ in which the jobs of $I$ form a consecutive subsequence preceding all other jobs of $M$:
--   $$\tau=\alpha\,\beta\,\gamma,\qquad \{\text{jobs of }\beta\}=I,\qquad M\setminus I\subseteq\{\text{jobs of }\gamma\}.$$
--
--   This is the result behind composite jobs: once a $\rho$-maximal initial set is identified, its jobs may be merged into a single job.
--
--   **Formalization Note** $\rho$-maximal initial sets are nonempty and are compared with nonempty initial sets only ($\rho(\emptyset)=0$ in Lean). The page remarks that Sidney states this for a minimal $\rho$-maximal initial set of $N$; the statement here is the page's, for an arbitrary $\rho$-maximal initial set of an arbitrary module.
-- source:
--   Lawler, Sequencing jobs to minimize total weighted completion time subject to precedence constraints, IRIA-LABORIA Rapport de Recherche No. 205 (Dec. 1976), HAL hal-04716371v1, p. 8, Theorem 2 (printed "Theroem 2")

import Mathlib
import Definitions.Def_LawlerWCT_SeriesPar_Model

namespace LawlerWCT.SeriesPar

theorem theorem_2 {ι : Type*} [DecidableEq ι] (N : Finset ι) (G : ι → ι → Prop)
    (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (p w : ι → ℝ) (hp : ∀ j ∈ N, 0 < p j)
    (M : Finset ι) (hM : IsModule G N M)
    (I : Finset ι) (hI : IsRhoMaximal G p w M I) :
    ∃ τ : List ι, SingleMachinePrec.Biclique.IsOptimalSchedule G p w N τ ∧
      ∃ a b c : List ι, τ = a ++ b ++ c ∧ (∀ j, j ∈ b ↔ j ∈ I) ∧
        ∀ m ∈ M, m ∉ I → m ∈ c := by sorry

end LawlerWCT.SeriesPar
