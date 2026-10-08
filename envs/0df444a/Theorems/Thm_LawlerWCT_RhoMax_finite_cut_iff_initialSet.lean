-- Prove2me | Theorems.Thm_LawlerWCT_RhoMax_finite_cut_iff_initialSet
-- name    : LawlerWCT.RhoMax.finite_cut_iff_initialSet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:56.870348+00:00
-- url     : https://prove2.me/theorems/a62813d8-0cc1-49b0-8e7b-827edc582e82
-- title:
--   §7, p. 14 — an (s,t) cutset of G* has finite capacity iff I = T − {t} is an initial set
-- statement:
--   Let $G=(N,A)$ be a digraph on a finite job set $N$, let $w_j$ be real weights, and let $G^*$ be the network obtained by adding a source $s$ and a sink $t$, with capacities $c_{sj}=\max(0,-w_j)$, $c_{jt}=\max(0,w_j)$ and $c_{ij}=+\infty$ on the arcs of $G$. Let $(S,T)$ be an $(s,t)$ cutset of $G^*$, i.e. a partition of the nodes of $G^*$ with $s\in S$ and $t\in T$, and let $I=T-\{t\}$. Then
--   $$c(S,T)<+\infty \iff I \text{ is an initial set of } N .$$
--
--   Since $T\mapsto T-\{t\}$ is injective, this is the one-to-one correspondence between finite-capacity cutsets of $G^*$ and initial sets of $G$ on which the minimum-cut method for maximum-weight initial sets rests.
--
--   **Formalization Note.** Initial sets are closed under predecessors along directed paths (Definition 2), while the cut only sees arcs; the hypothesis that every arc of $G$ joins two jobs of $N$ makes the two notions agree. A cutset is encoded by its sink side $T\subseteq\{s,t\}\cup N$ with $t\in T$, $s\notin T$; an infinite capacity is $\top$ in `WithTop ℝ`.
-- source:
--   Lawler, Sequencing jobs to minimize total weighted completion time subject to precedence constraints, IRIA-LABORIA Rapport de Recherche No. 205 (Dec. 1976), HAL hal-04716371v1, p. 14, §7, paragraph "There is a one-to-one correspondence between initial sets of G and finite-capacity cutsets of G*"

import Mathlib
import Definitions.Def_LawlerWCT_RhoMax_Model

namespace LawlerWCT.RhoMax

theorem finite_cut_iff_initialSet {ι : Type*} [DecidableEq ι] (N : Finset ι)
    (G : ι → ι → Prop) (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (w : ι → ℝ)
    (T : Finset (Node ι)) (hT : T ⊆ nodes N) (ht : Node.t ∈ T) (hs : Node.s ∉ T) :
    cutCapacity N G w T < ⊤ ↔ LawlerWCT.SeriesPar.IsInitialSet G N (jobsOf N T) := by sorry

end LawlerWCT.RhoMax
