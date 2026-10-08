-- Prove2me | Theorems.Thm_LawlerWCT_SeriesPar_theorem_1
-- name    : LawlerWCT.SeriesPar.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:56:48.92497+00:00
-- url     : https://prove2.me/theorems/a2d128c3-171d-4604-bcd8-f8260a327aa8
-- title:
--   Theorem 1, p. 7 — an optimal sequence of a module extends to an optimal sequence of N consistent with it
-- statement:
--   Throughout, $N$ is a finite set of jobs to be sequenced on a single machine, $G=(N,A)$ is an acyclic digraph on $N$ (job $i$ must precede job $j$ when there is a directed path from $i$ to $j$), job $j$ has a processing time $p_j>0$ and a real weight $w_j$, and the cost of a feasible sequence is $\sum_{j} w_j C_j$, where $C_j$ is the completion time of $j$ when the machine starts at time $0$ and never idles.
--
--   Let $M\subseteq N$ be a job module of $G$ (Definition 1) and let $\sigma$ be an optimal sequence for $M$, i.e. a sequence of the jobs of $M$ that respects the precedence constraints among them and minimizes $\sum_{j\in M}w_jC_j$ among such sequences. Then there is an optimal sequence $\tau$ for $N$ consistent with $\sigma$: the jobs of $M$ appear in $\tau$ in the same order as in $\sigma$,
--   $$\tau\ \text{optimal for } N\quad\text{and}\quad \tau|_M=\sigma .$$
--
--   This is Sidney's Lemma 23. It allows the subproblem on a module to be solved independently of the rest of the problem.
--
--   **Formalization Note** "Optimal sequence for $M$" is `IsOptimalSchedule G p w M σ`: feasibility only constrains pairs of jobs that both lie in the sequence, so this is the subproblem on $M$ with the induced constraints. "Consistent with $\sigma$" is `τ.filter (· ∈ M) = σ`. $G$ is an arbitrary acyclic digraph, not necessarily series parallel, as on the page.
-- source:
--   Lawler, Sequencing jobs to minimize total weighted completion time subject to precedence constraints, IRIA-LABORIA Rapport de Recherche No. 205 (Dec. 1976), HAL hal-04716371v1, p. 7, Theorem 1

import Mathlib
import Definitions.Def_LawlerWCT_SeriesPar_Model

namespace LawlerWCT.SeriesPar

theorem theorem_1 {ι : Type*} [DecidableEq ι] (N : Finset ι) (G : ι → ι → Prop)
    (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (p w : ι → ℝ) (hp : ∀ j ∈ N, 0 < p j)
    (M : Finset ι) (hM : IsModule G N M)
    (σ : List ι) (hσ : SingleMachinePrec.Biclique.IsOptimalSchedule G p w M σ) :
    ∃ τ : List ι, SingleMachinePrec.Biclique.IsOptimalSchedule G p w N τ ∧
      τ.filter (· ∈ M) = σ := by sorry

end LawlerWCT.SeriesPar
