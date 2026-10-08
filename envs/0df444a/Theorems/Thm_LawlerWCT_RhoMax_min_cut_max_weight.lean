-- Prove2me | Theorems.Thm_LawlerWCT_RhoMax_min_cut_max_weight
-- name    : LawlerWCT.RhoMax.min_cut_max_weight
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:58.372059+00:00
-- url     : https://prove2.me/theorems/2f8f6a5b-0736-4747-9acf-6e5754e4ba30
-- title:
--   §7, p. 15 — a minimum capacity (s,t) cutset of G* yields a maximum weight initial set
-- statement:
--   Let $G=(N,A)$ be a digraph on a finite job set $N$ with real weights $w_j$ of either sign, and let $G^*$ be the network of §7 (capacities $c_{sj}=\max(0,-w_j)$, $c_{jt}=\max(0,w_j)$, $c_{ij}=+\infty$ on the arcs of $G$). If $(S,T)$ is an $(s,t)$ cutset of minimum capacity among all $(s,t)$ cutsets of $G^*$, then $I=T-\{t\}$ is an initial set of $N$ and
--   $$\sum_{j\in I'}w_j\le\sum_{j\in I}w_j\qquad\text{for every initial set } I' \text{ of } N .$$
--
--   This turns the search for an initial set of maximum total weight, with weights of either sign, into a minimum-cut computation; it is the subroutine every trial value of the ratio uses.
--
--   **Formalization Note.** The maximum ranges over all initial sets, the empty one included (weight $0$); this is what a minimum cut delivers, because the cutset with $T=\{t\}$ is finite.
-- source:
--   Lawler, Sequencing jobs to minimize total weighted completion time subject to precedence constraints, IRIA-LABORIA Rapport de Recherche No. 205 (Dec. 1976), HAL hal-04716371v1, p. 15, §7, sentence "It follows that a minimum capacity (s,t) cutset yields a maximum weight initial set I."

import Mathlib
import Definitions.Def_LawlerWCT_RhoMax_Model

namespace LawlerWCT.RhoMax

theorem min_cut_max_weight {ι : Type*} [DecidableEq ι] (N : Finset ι)
    (G : ι → ι → Prop) (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (w : ι → ℝ)
    (T : Finset (Node ι)) (hT : T ⊆ nodes N) (ht : Node.t ∈ T) (hs : Node.s ∉ T)
    (hmin : ∀ T' : Finset (Node ι), T' ⊆ nodes N → Node.t ∈ T' → Node.s ∉ T' →
      cutCapacity N G w T ≤ cutCapacity N G w T') :
    LawlerWCT.SeriesPar.IsInitialSet G N (jobsOf N T) ∧
      ∀ I, LawlerWCT.SeriesPar.IsInitialSet G N I → ∑ j ∈ I, w j ≤ ∑ j ∈ jobsOf N T, w j := by sorry

end LawlerWCT.RhoMax
