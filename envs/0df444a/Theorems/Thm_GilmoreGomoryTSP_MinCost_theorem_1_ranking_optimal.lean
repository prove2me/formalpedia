-- Prove2me | Theorems.Thm_GilmoreGomoryTSP_MinCost_theorem_1_ranking_optimal
-- name    : GilmoreGomoryTSP.MinCost.theorem_1_ranking_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:45:04.025859+00:00
-- url     : https://prove2.me/theorems/f704725e-5470-4414-8050-5582c24fbe7f
-- title:
--   Theorem 1 — the permutation φ that ranks the A is a minimal cost permutation
-- statement:
--   Let $N=n+1$ jobs have starting states $A_i$ and final states $B_i$, numbered so that $j>i$ implies $B_j\ge B_i$. Let $f,g$ be locally integrable functions on $\mathbb R$ with $f(x)+g(x)\ge0$ for all $x$, and let $c(\psi)=\sum_i c_{i\psi(i)}$ be the cost (3) of a permutation $\psi$ with the changeover costs $c_{ij}$ of (1). If $\varphi$ ranks the $A$, that is $j>i$ implies $A_{\varphi(j)}\ge A_{\varphi(i)}$, then
--   $$c(\varphi)=\min_\psi c(\psi),$$
--   the minimum being taken over all permutations $\psi$ (not only tours).
--
--   This is the assignment relaxation of the problem: $\varphi$ is the starting point from which the minimal tour is built.
--
--   **Formalization Note** The conclusion is stated as $c(\varphi)\le c(\psi)$ for every permutation $\psi$. The paper's "any integrable functions" is read as local integrability on $\mathbb R$.
-- source:
--   Gilmore and Gomory, Sequencing a one state-variable machine, Oper. Res. 12 (1964), p. 659, Theorem 1

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model

namespace GilmoreGomoryTSP.MinCost

theorem theorem_1_ranking_optimal {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ) :
    ∀ ψ : Equiv.Perm (Fin (n + 1)), cost f g A B φ ≤ cost f g A B ψ := by sorry

end GilmoreGomoryTSP.MinCost
