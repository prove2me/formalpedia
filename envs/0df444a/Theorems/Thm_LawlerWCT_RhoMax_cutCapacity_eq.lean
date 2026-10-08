-- Prove2me | Theorems.Thm_LawlerWCT_RhoMax_cutCapacity_eq
-- name    : LawlerWCT.RhoMax.cutCapacity_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:06.973462+00:00
-- url     : https://prove2.me/theorems/f9a08fed-70e7-48ce-a0f1-9b0125a361fb
-- title:
--   §7, p. 15 — a finite cutset of G* has capacity Σ_{j∈N} max(0, w_j) − Σ_{j∈I} w_j
-- statement:
--   In the setting of the network $G^*$ (source $s$, sink $t$, capacities $c_{sj}=\max(0,-w_j)$, $c_{jt}=\max(0,w_j)$, and $c_{ij}=+\infty$ on the arcs of $G$), let $(S,T)$ be an $(s,t)$ cutset of finite capacity and let $I=T-\{t\}$. Then
--   $$c(S,T)=\sum_{j\in N}\max(0,w_j)-\sum_{j\in I}w_j .$$
--
--   The first sum does not depend on the cutset, so minimizing the capacity of a finite cutset is the same as maximizing the weight of the corresponding initial set.
--
--   **Formalization Note.** The capacity lives in `WithTop ℝ`; the identity is stated as the coercion of a real number, so no subtraction takes place in `WithTop ℝ`. The "constant" of the paper's display is $\sum_{j\in N}\max(0,w_j)$, read off its third line. The first line of the printed display writes $\sum_{j\in S}c_{sj}$ where the arcs from $s$ into $T$ are meant, $\sum_{j\in T}c_{sj}$, as the second line shows; the statement uses the corrected reading.
-- source:
--   Lawler, Sequencing jobs to minimize total weighted completion time subject to precedence constraints, IRIA-LABORIA Rapport de Recherche No. 205 (Dec. 1976), HAL hal-04716371v1, p. 15, §7, display beginning "Let (S,T) be a cutset with c(S,T) finite"

import Mathlib
import Definitions.Def_LawlerWCT_RhoMax_Model

namespace LawlerWCT.RhoMax

theorem cutCapacity_eq {ι : Type*} [DecidableEq ι] (N : Finset ι)
    (G : ι → ι → Prop) (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (w : ι → ℝ)
    (T : Finset (Node ι)) (hT : T ⊆ nodes N) (ht : Node.t ∈ T) (hs : Node.s ∉ T)
    (hfin : cutCapacity N G w T < ⊤) :
    cutCapacity N G w T =
      ((∑ j ∈ N, max 0 (w j) - ∑ j ∈ jobsOf N T, w j : ℝ) : WithTop ℝ) := by sorry

end LawlerWCT.RhoMax
