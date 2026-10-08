-- Prove2me | Theorems.Thm_GilmoreGomoryTSP_MinCost_lemma_1_merge_cycles
-- name    : GilmoreGomoryTSP.MinCost.lemma_1_merge_cycles
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:44:54.875539+00:00
-- url     : https://prove2.me/theorems/bc54cd84-1d88-406b-8159-220bd52eb480
-- title:
--   Lemma 1 — an interchange between two cycles merges them into one
-- statement:
--   Let $\psi$ be a permutation of the jobs with cycles $C_1,\dots,C_p$ (fixed points count as cycles of length one), and let $\alpha_{ij}$ be an interchange with $i\in C_r$, $j\in C_s$, $r\ne s$. Then $\psi\alpha_{ij}$ has the same cycles as $\psi$ except that $C_r$ and $C_s$ are replaced by a single cycle containing all their nodes. Equivalently, for all jobs $k,l$: $k$ and $l$ lie in the same cycle of $\psi\alpha_{ij}$ if and only if they lie in the same cycle of $\psi$, or one of them lies in $C_r$ and the other in $C_s$.
--
--   Repeated use of this fact turns the cycles of $\varphi$ into a single tour (Theorem 2).
--
--   **Formalization Note** Cycles are encoded by Mathlib's `Equiv.Perm.SameCycle` ($k$ and $l$ are in the same cycle iff $l=\psi^m(k)$ for some integer $m$), and the conclusion is stated as the equivalence above for all $k,l$. $\psi\alpha_{ij}$ is `ψ * alpha i j`.
-- source:
--   Gilmore and Gomory, Sequencing a one state-variable machine, Oper. Res. 12 (1964), p. 660, Lemma 1

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model

namespace GilmoreGomoryTSP.MinCost

theorem lemma_1_merge_cycles {n : ℕ} (ψ : Equiv.Perm (Fin (n + 1))) (i j : Fin (n + 1))
    (hij : ¬ ψ.SameCycle i j) (k l : Fin (n + 1)) :
    (ψ * alpha i j).SameCycle k l ↔
      ψ.SameCycle k l ∨ (ψ.SameCycle k i ∧ ψ.SameCycle l j) ∨
        (ψ.SameCycle k j ∧ ψ.SameCycle l i) := by sorry

end GilmoreGomoryTSP.MinCost
