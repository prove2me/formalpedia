-- Prove2me | Theorems.Thm_LawlerWCT_SeriesPar_exists_rhoMaximal
-- name    : LawlerWCT.SeriesPar.exists_rhoMaximal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:56:56.751353+00:00
-- url     : https://prove2.me/theorems/a2b7f019-0c5c-4a3b-9035-9776f9f206ca
-- title:
--   Definition 3, p. 8 — every module admits a ρ-maximal initial set
-- statement:
--   Throughout, $N$ is a finite set of jobs to be sequenced on a single machine, $G=(N,A)$ is an acyclic digraph on $N$ (job $i$ must precede job $j$ when there is a directed path from $i$ to $j$), job $j$ has a processing time $p_j>0$ and a real weight $w_j$, and the cost of a feasible sequence is $\sum_{j} w_j C_j$, where $C_j$ is the completion time of $j$ when the machine starts at time $0$ and never idles.
--
--   Let $M$ be a job module of $G$. Then $M$ admits at least one $\rho$-maximal initial set: there is a nonempty initial set $I^*$ of $M$ with
--   $$\rho(I^*)\ \ge\ \rho(I)\qquad\text{for every nonempty initial set } I \text{ of } M,$$
--   where $\rho(I)=\sum_{j\in I}w_j\big/\sum_{j\in I}p_j$.
--
--   This guarantees that the hypothesis of Theorem 2 can always be met.
--
--   **Formalization Note** Since Lean evaluates $\rho(\emptyset)=0/0$ as $0$, $\rho$-maximality compares only nonempty initial sets and requires $I^*$ nonempty.
-- source:
--   Lawler, Sequencing jobs to minimize total weighted completion time subject to precedence constraints, IRIA-LABORIA Rapport de Recherche No. 205 (Dec. 1976), HAL hal-04716371v1, p. 8, Definition 3, sentence "Every module M admits at least one ρ-maximal initial set"

import Mathlib
import Definitions.Def_LawlerWCT_SeriesPar_Model

namespace LawlerWCT.SeriesPar

theorem exists_rhoMaximal {ι : Type*} [DecidableEq ι] (N : Finset ι) (G : ι → ι → Prop)
    (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (p w : ι → ℝ) (hp : ∀ j ∈ N, 0 < p j)
    (M : Finset ι) (hM : IsModule G N M) :
    ∃ I : Finset ι, IsRhoMaximal G p w M I := by sorry

end LawlerWCT.SeriesPar
