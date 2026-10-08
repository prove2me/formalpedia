-- Prove2me | Theorems.Thm_GilmoreGomoryTSP_MinCost_theorem_7_one_sided
-- name    : GilmoreGomoryTSP.MinCost.theorem_7_one_sided
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:45:00.705981+00:00
-- url     : https://prove2.me/theorems/e5fdbe4d-5280-435b-8f88-47ef53d892b0
-- title:
--   Theorem 7 — a minimal tour for (f, g) is minimal for (f + g, 0)
-- statement:
--   Let $f,g$ be locally integrable with $f+g\ge0$ and $A_i,B_i$ the states of the jobs. Let $\psi^*$ be a minimal cost tour for the cost functions $f$ and $g$: $\psi^*$ is a tour and $c_{f,g}(\psi^*)\le c_{f,g}(\psi)$ for every tour $\psi$. Then $\psi^*$ is still a minimal cost tour in the problem obtained by replacing $f(x)$ by $f(x)+g(x)$ and $g(x)$ by $0$:
--   $$c_{f+g,\,0}(\psi^*)\le c_{f+g,\,0}(\psi)\quad\text{for every tour }\psi.$$
--
--   It reduces the general problem to the one-sided case in which decreasing the state is free.
--
--   **Formalization Note** $c_{f,g}$ denotes the cost (3) computed with the densities $f,g$ in (1). The paper proves this for the tour produced by the algorithm; it is stated here, as printed, for any minimal cost tour. The numbering of the $B$ plays no role and is not assumed.
-- source:
--   Gilmore and Gomory, Sequencing a one state-variable machine, Oper. Res. 12 (1964), p. 677, Theorem 7

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model

namespace GilmoreGomoryTSP.MinCost

theorem theorem_7_one_sided {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ)
    (ψs : Equiv.Perm (Fin (n + 1))) (hψs : IsTour ψs)
    (hmin : ∀ ψ : Equiv.Perm (Fin (n + 1)), IsTour ψ → cost f g A B ψs ≤ cost f g A B ψ) :
    ∀ ψ : Equiv.Perm (Fin (n + 1)), IsTour ψ →
      cost (fun x => f x + g x) (fun _ => 0) A B ψs ≤
        cost (fun x => f x + g x) (fun _ => 0) A B ψ := by sorry

end GilmoreGomoryTSP.MinCost
