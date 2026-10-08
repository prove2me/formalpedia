-- Prove2me | Theorems.Thm_LawlerWCT_SeriesPar_series_composition_procedure
-- name    : LawlerWCT.SeriesPar.series_composition_procedure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:59:10.564998+00:00
-- url     : https://prove2.me/theorems/bb80a288-bc04-4ba9-bfa4-35508ad88ef7
-- title:
--   §5, pp. 10–11 — series composition by Steps 1–3 yields a set representing an optimal sequence
-- statement:
--   Throughout, $N$ is a finite set of jobs to be sequenced on a single machine, $G=(N,A)$ is an acyclic digraph on $N$ (job $i$ must precede job $j$ when there is a directed path from $i$ to $j$), job $j$ has a processing time $p_j>0$ and a real weight $w_j$, and the cost of a feasible sequence is $\sum_{j} w_j C_j$, where $C_j$ is the completion time of $j$ when the machine starts at time $0$ and never idles.
--
--   Say that a set $F$ of composite jobs *represents an optimal sequence* for a set of jobs $M$ if every composite job of $F$ is a nonempty sequence each of whose nonempty proper prefixes has ratio at most its own, the composite jobs of $F$ partition $M$, and every arrangement of $F$ in nonincreasing ratio order, expanded into a sequence of jobs, is an optimal sequence for $M$ (under the constraints of $G$ among the jobs of $M$).
--
--   Let $M_1,M_2\subseteq N$ be disjoint modules of $G$ whose union $M_1\cup M_2$ is also a module (the sons of a node of the decomposition tree and the node itself), with every job of $M_1$ required to precede every job of $M_2$, and let $F_1$ and $F_2$ represent optimal sequences for $M_1$ and $M_2$. Let $F$ be the result of any run of the series procedure (Steps 1–3, p. 11) on $F_1$ and $F_2$: Step 1 compares a minimal-ratio $i\in F_1$ with a maximal-ratio $j\in F_2$ and halts with $F_1\cup F_2$ if $\rho(i)>\rho(j)$, and otherwise forms $k=(i,j)$; Step 2 repeatedly absorbs a minimal-ratio $i$ of the rest of $F_1$ as $k=(i,k)$ while $\rho(i)\le\rho(k)$; Step 3 halts with $F_1\cup F_2\cup\{k\}$ if a maximal-ratio $j$ of the rest of $F_2$ has $\rho(k)>\rho(j)$, and otherwise absorbs it as $k=(k,j)$ and returns to Step 2. Then
--   $$F\ \text{represents an optimal sequence for}\ M_1\cup M_2 .$$
--
--   This is the heart of the series parallel algorithm: the series step, which forms composite jobs, preserves optimality of the ratio order.
--
--   **Formalization Note** The procedure is the inductive relation `SeriesMerge` / `SeriesLoop`; every tie-breaking among minimal or maximal elements is allowed. The dummies of ratio $\pm\infty$ are encoded by vacuous conditions on empty sets. The page's $M_1$, $M_2$ and $M=M_1\cup M_2$ are modules (§5, p. 9: "an optimal sequence for a module $M$ from previously determined optimal sequences for its sons, $M_1$ and $M_2$"); the module hypotheses are needed, since otherwise a path $i\to x\to j$ through a job $x\notin M$ would constrain $M$ without being visible to feasibility on $M$.
-- source:
--   Lawler, Sequencing jobs to minimize total weighted completion time subject to precedence constraints, IRIA-LABORIA Rapport de Recherche No. 205 (Dec. 1976), HAL hal-04716371v1, pp. 10–11, §5, paragraphs "Now suppose ρ(i) ≤ ρ(j)" and "Now let us find the next minimal element", and Steps 1–3

import Mathlib
import Definitions.Def_LawlerWCT_SeriesPar_Model

namespace LawlerWCT.SeriesPar

theorem series_composition_procedure {ι : Type*} [DecidableEq ι] (N : Finset ι) (G : ι → ι → Prop)
    (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (p w : ι → ℝ) (hp : ∀ j ∈ N, 0 < p j)
    (M₁ M₂ : Finset ι) (hdisj : Disjoint M₁ M₂)
    (hM₁ : IsModule G N M₁) (hM₂ : IsModule G N M₂) (hM : IsModule G N (M₁ ∪ M₂))
    (hser : ∀ i ∈ M₁, ∀ j ∈ M₂, Relation.TransGen G i j)
    (F₁ F₂ : List (List ι)) (h₁ : Represents G p w M₁ F₁) (h₂ : Represents G p w M₂ F₂)
    (F : List (List ι)) (hmerge : SeriesMerge p w F₁ F₂ F) :
    Represents G p w (M₁ ∪ M₂) F := by sorry

end LawlerWCT.SeriesPar
