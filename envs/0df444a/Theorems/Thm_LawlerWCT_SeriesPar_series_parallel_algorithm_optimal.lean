-- Prove2me | Theorems.Thm_LawlerWCT_SeriesPar_series_parallel_algorithm_optimal
-- name    : LawlerWCT.SeriesPar.series_parallel_algorithm_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:58:55.933214+00:00
-- url     : https://prove2.me/theorems/dccdbb9e-bbd9-468a-8822-1df3cd683359
-- title:
--   §5, pp. 9–12 — composite jobs of a run of the series parallel algorithm, in nonincreasing ratio order, form an optimal sequence
-- statement:
--   Throughout, $N$ is a finite set of jobs to be sequenced on a single machine, $G=(N,A)$ is an acyclic digraph on $N$ (job $i$ must precede job $j$ when there is a directed path from $i$ to $j$), job $j$ has a processing time $p_j>0$ and a real weight $w_j$, and the cost of a feasible sequence is $\sum_{j} w_j C_j$, where $C_j$ is the completion time of $j$ when the machine starts at time $0$ and never idles.
--
--   Let $T$ be a decomposition tree of $G$: its leaves are exactly the jobs of $N$, each occurring once, and for all $i,j\in N$, job $i$ must precede job $j$ in $G$ if and only if $(i,j)$ is an arc of the transitive series parallel digraph built by $T$ (that is, the transitive closure of $G$ is the digraph $T$ builds; $G$ is *series parallel*).
--
--   Run the series parallel algorithm bottom-up on $T$ (a leaf yields its job, a $P$-node the union of its sons' sets, an $S$-node the result of the series procedure, Steps 1–3 of p. 11, on its sons' sets), with any tie-breaking, and let $F$ be the set of composite jobs it produces for the root. List the composite jobs of $F$ in nonincreasing order of their ratios
--   $$\rho(c)=\frac{\sum_{j\in c}w_j}{\sum_{j\in c}p_j},$$
--   breaking ties arbitrarily, and replace each composite job by the sequence of jobs built up for it. The resulting sequence is an optimal sequence for $N$: it respects every precedence constraint and minimizes $\sum_{j\in N}w_jC_j$ among all feasible sequences.
--
--   This is the correctness of Lawler's algorithm, which solves the problem for series parallel precedence constraints in $O(n\log n)$ time once a decomposition tree is known.
--
--   **Formalization Note** The decomposition tree is tied to $G$ by three hypotheses: its leaves are distinct, they are exactly $N$, and the transitive closure of $G$ on $N$ coincides with the arc relation of the transitive series parallel digraph built by the tree. Feasibility and the objective are those of $G$ itself, not of the tree. The weights are arbitrary reals and the processing times positive; $\rho(\emptyset)$ never occurs, since composite jobs are nonempty.
-- source:
--   Lawler, Sequencing jobs to minimize total weighted completion time subject to precedence constraints, IRIA-LABORIA Rapport de Recherche No. 205 (Dec. 1976), HAL hal-04716371v1, pp. 9–12, §5, final paragraph "At the end of the computation, an optimal sequence is found by listing the jobs in the set N in nonincreasing ratio order"

import Mathlib
import Definitions.Def_LawlerWCT_SeriesPar_Model

namespace LawlerWCT.SeriesPar

theorem series_parallel_algorithm_optimal {ι : Type*} [DecidableEq ι] (N : Finset ι) (G : ι → ι → Prop)
    (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (p w : ι → ℝ) (hp : ∀ j ∈ N, 0 < p j)
    (T : SPTree ι) (hT : T.leaves.Nodup) (hTN : ∀ j, j ∈ T.leaves ↔ j ∈ N)
    (hTG : ∀ i ∈ N, ∀ j ∈ N, Relation.TransGen G i j ↔ T.prec i j)
    (F : List (List ι)) (hrun : Run p w T F)
    (L : List (List ι)) (hL : L.Perm F) (hord : IsRatioOrder p w L) :
    SingleMachinePrec.Biclique.IsOptimalSchedule G p w N L.flatten := by sorry

end LawlerWCT.SeriesPar
