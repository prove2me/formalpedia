-- Prove2me | Theorems.Thm_LawlerWCT_SeriesPar_subtree_isModule
-- name    : LawlerWCT.SeriesPar.subtree_isModule
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:57:55.369547+00:00
-- url     : https://prove2.me/theorems/2dc12b9c-55b2-4ee1-8838-143cc781f691
-- title:
--   §4, p. 7 — the leaves of every subtree of a decomposition tree form a module
-- statement:
--   Throughout, $N$ is a finite set of jobs to be sequenced on a single machine, $G=(N,A)$ is an acyclic digraph on $N$ (job $i$ must precede job $j$ when there is a directed path from $i$ to $j$), job $j$ has a processing time $p_j>0$ and a real weight $w_j$, and the cost of a feasible sequence is $\sum_{j} w_j C_j$, where $C_j$ is the completion time of $j$ when the machine starts at time $0$ and never idles.
--
--   Let $T$ be a decomposition tree of $G$: its leaves are exactly the jobs of $N$, each occurring once, and for all $i,j\in N$, job $i$ must precede job $j$ in $G$ if and only if $(i,j)$ is an arc of the transitive series parallel digraph built by $T$ (that is, the transitive closure of $G$ is the digraph $T$ builds; $G$ is *series parallel*).
--
--   Then for every subtree $S$ of $T$ (the subtree rooted at any node of $T$), the set of leaves of $S$ is a module of $G$:
--   $$\operatorname{leaves}(S)\ \text{is a job module of } G=(N,A).$$
--
--   This is what lets the series parallel algorithm treat each node of the decomposition tree as an independent subproblem, to which Sidney's Theorems 1 and 2 apply.
--
--   **Formalization Note** The processing times and weights play no role and are omitted. Modules use the disjunction of (4.1)–(4.3), which is "exactly one" for acyclic $G$.
-- source:
--   Lawler, Sequencing jobs to minimize total weighted completion time subject to precedence constraints, IRIA-LABORIA Rapport de Recherche No. 205 (Dec. 1976), HAL hal-04716371v1, p. 7, §4, paragraph "What is important for our purposes"

import Mathlib
import Definitions.Def_LawlerWCT_SeriesPar_Model

namespace LawlerWCT.SeriesPar

theorem subtree_isModule {ι : Type*} [DecidableEq ι] (N : Finset ι) (G : ι → ι → Prop)
    (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (T : SPTree ι) (hT : T.leaves.Nodup) (hTN : ∀ j, j ∈ T.leaves ↔ j ∈ N)
    (hTG : ∀ i ∈ N, ∀ j ∈ N, Relation.TransGen G i j ↔ T.prec i j)
    (S : SPTree ι) (hS : S.IsSubtree T) :
    IsModule G N S.leaves.toFinset := by sorry

end LawlerWCT.SeriesPar
