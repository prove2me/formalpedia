-- Prove2me | Theorems.Thm_GilmoreGomoryTSP_MinCost_eq_28_tree_le_costStar
-- name    : GilmoreGomoryTSP.MinCost.eq_28_tree_le_costStar
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:02:11.131954+00:00
-- url     : https://prove2.me/theorems/014e228f-15b5-4fa7-a1b5-32b5e0e4342b
-- title:
--   Eq. (28) — for every tour ψ, c*(ψ) ≥ c_φ(τ) for a minimal cost tree τ
-- statement:
--   Let $B$ be sorted, $f,g$ locally integrable with $f+g\ge0$, $\varphi$ a permutation ranking the $A$, and $\tau$ a minimal cost spanning tree of $G_\varphi$ made of arcs $R_{q,q+1}$. For every tour $\psi$,
--   $$c^*(\psi)\ge c_\varphi(\tau).$$
--
--   Together with Theorems 3 and 4 this gives $c(\psi)\ge c(\varphi)+c^*(\psi)\ge c(\varphi)+c_\varphi(\tau)=c(\psi^*)$, i.e. (29).
--
--   **Formalization Note** $\psi$ ranges over tours only; for a non-tour permutation (e.g. $\psi=\varphi$, where $c^*(\varphi)=0$) the inequality can fail.
-- source:
--   Gilmore and Gomory, Sequencing a one state-variable machine, Oper. Res. 12 (1964), p. 669, Eq. (28)

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model
import Definitions.Def_GilmoreGomoryTSP_MinCost_Underestimate

namespace GilmoreGomoryTSP.MinCost

theorem eq_28_tree_le_costStar {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ)
    (ψ : Equiv.Perm (Fin (n + 1))) (hψ : IsTour ψ)
    (T : Finset (Fin n)) (hT : IsMinCostAdjTree f g A B φ T) :
    adjTreeCost f g A B φ T ≤ costStar f g A B φ ψ := by sorry

end GilmoreGomoryTSP.MinCost
