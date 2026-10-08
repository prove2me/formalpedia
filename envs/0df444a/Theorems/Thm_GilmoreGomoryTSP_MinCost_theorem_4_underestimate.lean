-- Prove2me | Theorems.Thm_GilmoreGomoryTSP_MinCost_theorem_4_underestimate
-- name    : GilmoreGomoryTSP.MinCost.theorem_4_underestimate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:01:32.287237+00:00
-- url     : https://prove2.me/theorems/21d41c98-c2dd-4bac-82cb-412d98a4fbd9
-- title:
--   Theorem 4 — the underestimate c(ψ) ≥ c(φ) + c*(ψ) for every permutation
-- statement:
--   Let $B$ be sorted, $f,g$ locally integrable with $f+g\ge0$, $\varphi$ a permutation ranking the $A$, and $c^*$ the underestimating cost (17) built from the set $P=\bigcup_q P_q$. For any permutation $\psi$,
--   $$c(\psi)\ge c(\varphi)+c^*(\psi).$$
--
--   Combined with a lower bound of $c^*(\psi)$ by the cost of a spanning tree for tours $\psi$ (Eq. (28)), this gives the optimality of $\psi^*$.
--
--   **Formalization Note** $\psi$ ranges over all permutations, not only tours, as in the paper.
-- source:
--   Gilmore and Gomory, Sequencing a one state-variable machine, Oper. Res. 12 (1964), p. 666, Theorem 4

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model
import Definitions.Def_GilmoreGomoryTSP_MinCost_Underestimate

namespace GilmoreGomoryTSP.MinCost

theorem theorem_4_underestimate {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ) :
    ∀ ψ : Equiv.Perm (Fin (n + 1)),
      cost f g A B φ + costStar f g A B φ ψ ≤ cost f g A B ψ := by sorry

end GilmoreGomoryTSP.MinCost
