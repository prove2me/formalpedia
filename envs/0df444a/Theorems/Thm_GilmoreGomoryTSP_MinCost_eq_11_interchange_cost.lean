-- Prove2me | Theorems.Thm_GilmoreGomoryTSP_MinCost_eq_11_interchange_cost
-- name    : GilmoreGomoryTSP.MinCost.eq_11_interchange_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:44:40.652002+00:00
-- url     : https://prove2.me/theorems/df978a70-2d2b-4b41-a639-969b47e58ffa
-- title:
--   Eq. (11) — the cost of an interchange under the order-preserving assumption (8)
-- statement:
--   Let $f,g$ be locally integrable with $f+g\ge0$, let $A_i,B_i$ be the states of the jobs and $\psi$ any permutation. For jobs $i,j$ assume (8): $B_j\ge B_i$ and $A_{\psi(j)}\ge A_{\psi(i)}$. Then the cost of the interchange $\alpha_{ij}$ is
--   $$c_\psi(\alpha_{ij}) = c_{i\psi(j)}+c_{j\psi(i)}-c_{i\psi(i)}-c_{j\psi(j)} = \big\|[B_i,B_j]\cap[A_{\psi(i)},A_{\psi(j)}]\big\|,$$
--   where $\|[a,b]\| = \int_a^b \{f(x)+g(x)\}\,dx$ (and $\|\emptyset\|=0$).
--
--   In particular $c_\psi(\alpha_{ij})\ge0$ for interchanges that create a crossing; this formula is the computational core of the algorithm (step P4).
--
--   **Formalization Note** The right-hand side is the set integral of $f+g$ over $[B_i,B_j]\cap[A_{\psi(i)},A_{\psi(j)}]$, which is $0$ when the intersection is empty or a point. The case "with the reverse order, preceded by a minus sign" is not part of this item.
-- source:
--   Gilmore and Gomory, Sequencing a one state-variable machine, Oper. Res. 12 (1964), p. 659, Eqs. (8) and (11)

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model

namespace GilmoreGomoryTSP.MinCost

theorem eq_11_interchange_cost {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ)
    (ψ : Equiv.Perm (Fin (n + 1))) (i j : Fin (n + 1))
    (hBij : B i ≤ B j) (hAij : A (ψ i) ≤ A (ψ j)) :
    interchangeCost f g A B ψ i j =
      ∫ x in Set.Icc (B i) (B j) ∩ Set.Icc (A (ψ i)) (A (ψ j)), (f x + g x) := by sorry

end GilmoreGomoryTSP.MinCost
