-- Prove2me | Theorems.Thm_LawlerWCT_SeriesPar_series_composition_union
-- name    : LawlerWCT.SeriesPar.series_composition_union
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:58:52.250916+00:00
-- url     : https://prove2.me/theorems/28340604-26f0-4753-a91c-95a8e7811d17
-- title:
--   §5, p. 10 — series composition when min ratio in M₁ exceeds max ratio in M₂: the union represents an optimal sequence
-- statement:
--   Throughout, $N$ is a finite set of jobs to be sequenced on a single machine, $G=(N,A)$ is an acyclic digraph on $N$ (job $i$ must precede job $j$ when there is a directed path from $i$ to $j$), job $j$ has a processing time $p_j>0$ and a real weight $w_j$, and the cost of a feasible sequence is $\sum_{j} w_j C_j$, where $C_j$ is the completion time of $j$ when the machine starts at time $0$ and never idles.
--
--   Say that a set $F$ of composite jobs *represents an optimal sequence* for a set of jobs $M$ if every composite job of $F$ is a nonempty sequence each of whose nonempty proper prefixes has ratio at most its own, the composite jobs of $F$ partition $M$, and every arrangement of $F$ in nonincreasing ratio order, expanded into a sequence of jobs, is an optimal sequence for $M$ (under the constraints of $G$ among the jobs of $M$).
--
--   Let $M_1,M_2\subseteq N$ be disjoint modules of $G$ whose union $M_1\cup M_2$ is also a module (the sons of a node of the decomposition tree and the node itself), with every job of $M_1$ required to precede every job of $M_2$. Let $F_1$ represent an optimal sequence for $M_1$ and $F_2$ one for $M_2$, and suppose a minimum-ratio composite job of $F_1$ has larger ratio than a maximum-ratio composite job of $F_2$, i.e.
--   $$\rho(c)>\rho(d)\qquad\text{for all } c\in F_1,\ d\in F_2 .$$
--   Then $F_1\cup F_2$ represents an optimal sequence for $M_1\cup M_2$.
--
--   This is the easy case of the series step of the algorithm.
--
--   **Formalization Note** The composite invariant is part of "represents" (see the parallel composition milestone).
-- source:
--   Lawler, Sequencing jobs to minimize total weighted completion time subject to precedence constraints, IRIA-LABORIA Rapport de Recherche No. 205 (Dec. 1976), HAL hal-04716371v1, p. 10, §5, paragraph "For series composition of M₁ and M₂"

import Mathlib
import Definitions.Def_LawlerWCT_SeriesPar_Model

namespace LawlerWCT.SeriesPar

theorem series_composition_union {ι : Type*} [DecidableEq ι] (N : Finset ι) (G : ι → ι → Prop)
    (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (p w : ι → ℝ) (hp : ∀ j ∈ N, 0 < p j)
    (M₁ M₂ : Finset ι) (hdisj : Disjoint M₁ M₂)
    (hM₁ : IsModule G N M₁) (hM₂ : IsModule G N M₂) (hM : IsModule G N (M₁ ∪ M₂))
    (hser : ∀ i ∈ M₁, ∀ j ∈ M₂, Relation.TransGen G i j)
    (F₁ F₂ : List (List ι)) (h₁ : Represents G p w M₁ F₁) (h₂ : Represents G p w M₂ F₂)
    (hratio : ∀ c ∈ F₁, ∀ d ∈ F₂, crho p w d < crho p w c) :
    Represents G p w (M₁ ∪ M₂) (F₁ ++ F₂) := by sorry

end LawlerWCT.SeriesPar
