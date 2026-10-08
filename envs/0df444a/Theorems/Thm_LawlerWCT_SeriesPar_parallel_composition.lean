-- Prove2me | Theorems.Thm_LawlerWCT_SeriesPar_parallel_composition
-- name    : LawlerWCT.SeriesPar.parallel_composition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:59:01.902566+00:00
-- url     : https://prove2.me/theorems/405f708b-30b4-4bf9-a1cd-4b1bcc56e140
-- title:
--   §5, p. 10 — parallel composition: the union of the two sets represents an optimal sequence
-- statement:
--   Throughout, $N$ is a finite set of jobs to be sequenced on a single machine, $G=(N,A)$ is an acyclic digraph on $N$ (job $i$ must precede job $j$ when there is a directed path from $i$ to $j$), job $j$ has a processing time $p_j>0$ and a real weight $w_j$, and the cost of a feasible sequence is $\sum_{j} w_j C_j$, where $C_j$ is the completion time of $j$ when the machine starts at time $0$ and never idles.
--
--   Say that a set $F$ of composite jobs *represents an optimal sequence* for a set of jobs $M$ if every composite job of $F$ is a nonempty sequence each of whose nonempty proper prefixes has ratio at most its own, the composite jobs of $F$ partition $M$, and every arrangement of $F$ in nonincreasing ratio order, expanded into a sequence of jobs, is an optimal sequence for $M$ (under the constraints of $G$ among the jobs of $M$).
--
--   Let $M_1,M_2\subseteq N$ be disjoint modules of $G$ whose union $M_1\cup M_2$ is also a module (the sons of a node of the decomposition tree and the node itself), with no job of $M_1$ constrained with respect to any job of $M_2$ (neither must precede the other). If $F_1$ represents an optimal sequence for $M_1$ and $F_2$ one for $M_2$, then
--   $$F_1\cup F_2\ \text{represents an optimal sequence for}\ M_1\cup M_2 .$$
--
--   This is the parallel step of the algorithm: for a $P$-node of the decomposition tree nothing has to be computed.
--
--   **Formalization Note** The composite invariant (every proper prefix has ratio at most the whole) is part of "represents". Without it the claim fails: with $a,b$ unconstrained, $(w,p)=(2,1),(0,1)$, the single composite $(a,b)$ is an optimal sequence for $\{a,b\}$, but with an independent $x$ of $(w,p)=(1.5,1)$ the ratio order $x,a,b$ costs $5.5$ while $a,x,b$ costs $5$. The page's composite jobs are $\rho$-maximal initial sets (p. 9), which is this invariant.
-- source:
--   Lawler, Sequencing jobs to minimize total weighted completion time subject to precedence constraints, IRIA-LABORIA Rapport de Recherche No. 205 (Dec. 1976), HAL hal-04716371v1, p. 10, §5, paragraph "For parallel composition of M₁ and M₂"

import Mathlib
import Definitions.Def_LawlerWCT_SeriesPar_Model

namespace LawlerWCT.SeriesPar

theorem parallel_composition {ι : Type*} [DecidableEq ι] (N : Finset ι) (G : ι → ι → Prop)
    (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (p w : ι → ℝ) (hp : ∀ j ∈ N, 0 < p j)
    (M₁ M₂ : Finset ι) (hdisj : Disjoint M₁ M₂)
    (hM₁ : IsModule G N M₁) (hM₂ : IsModule G N M₂) (hM : IsModule G N (M₁ ∪ M₂))
    (hunc : ∀ i ∈ M₁, ∀ j ∈ M₂, ¬ Relation.TransGen G i j ∧ ¬ Relation.TransGen G j i)
    (F₁ F₂ : List (List ι)) (h₁ : Represents G p w M₁ F₁) (h₂ : Represents G p w M₂ F₂) :
    Represents G p w (M₁ ∪ M₂) (F₁ ++ F₂) := by sorry

end LawlerWCT.SeriesPar
