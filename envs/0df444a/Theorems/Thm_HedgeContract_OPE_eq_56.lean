-- Prove2me | Theorems.Thm_HedgeContract_OPE_eq_56
-- name    : HedgeContract.OPE.eq_56
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:53.87387+00:00
-- url     : https://prove2.me/theorems/fe360202-452e-4ed6-b24f-2fc8f75b6b31
-- title:
--   (56), p. 32 (PDF 34) — clamped effort minimizes net effort cost
-- statement:
--   Let $\kappa>0$ and $\underline A\le\overline A$. For every sensitivity $Z\in\mathbb R$, the clamped response $A^*(Z)$ in equation (56) belongs to $[\underline A,\overline A]$ and satisfies
--
--   $$h(A^*(Z))-ZA^*(Z)\le h(A)-ZA\qquad\text{for every }A\in[\underline A,\overline A].$$
--
--   Thus the formula defining $A^*$ really gives the manager's constrained best response; later results may use the same response without reintroducing the minimization problem.
--
--   **Formalization Note.** The endpoint cases agree because $h'(A)=\kappa A+b$.
-- source:
--   Huang, Ju & Xing, Optimal Contracting with Unobservable Managerial Hedging, working paper (Nov. 14, 2017), p. 32 (PDF 34), §6.6, equation (56)

import Mathlib
import Definitions.Def_HedgeContract_OPE_Model
set_option autoImplicit false

namespace HedgeContract.OPE
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-- Equation (56): the clamped effort is a minimizer of the net effort cost. -/
theorem eq_56 (P : Params) (Z : ℝ) (hκ : 0 < P.κ) (hA : P.Alo ≤ P.Ahi) :
    Astar P Z ∈ Set.Icc P.Alo P.Ahi ∧
      ∀ A ∈ Set.Icc P.Alo P.Ahi,
        h P (Astar P Z) - Z * Astar P Z ≤ h P A - Z * A := by sorry

end HedgeContract.OPE
