-- Prove2me | Theorems.Thm_MDPFinance_POMDP_theorem_5_3_2
-- name    : MDPFinance.POMDP.theorem_5_3_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:15:43.864647+00:00
-- url     : https://prove2.me/theorems/60dee151-906c-493b-b923-ab0962c41e39
-- title:
--   Theorem 5.3.2 — value equality between the POMDP and its filtered reformulation
-- statement:
--   For $\pi\in\Pi_N$ and $x\in E_X$: $J_N^\pi(x) = J_{N\pi}'(x,Q_0)$, and hence
--   $J_N(x) = J_N'(x,Q_0)$.
--
--   This is the reduction's linchpin: the filtered model is not merely *analogous* to the POMDP, it
--   has *exactly the same value*, for every policy and hence at the optimum — so solving the
--   filtered model (an ordinary Chapter-2 Markov Decision Model) solves the POMDP outright.
--
--   **Formalization Note.** Both value functions are evaluated at the filtered state $(x,Q_0)$ —
--   $Q_0$ packaged as `⟨M.Q0, M.isProbQ0⟩ : ProbabilityMeasure E_Y` — matching the book's own use of
--   the *initial* filter as the correct starting point for the equivalence; `Jprime`'s ability to
--   start from an arbitrary $\rho$ (not just $Q_0$) is exactly what lets `theorem_5_3_3` state a
--   Bellman equation at every reachable state, not just the initial one.
--
--   **Moderation note.** Stated in $[-\infty,\infty]$ under the section's standing Integrability Assumption (`hInt`), which the book assumes throughout the chapter (p. 151).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 157, PDF 171, Theorem 5.3.2

import Mathlib
import Definitions.Def_MDPFinance_POMDP_Model
import Definitions.Def_MDPFinance_POMDP_Policy
import Definitions.Def_MDPFinance_POMDP_Objective
import Definitions.Def_MDPFinance_POMDP_FilterData
import Definitions.Def_MDPFinance_POMDP_FilteredModel

open MeasureTheory ProbabilityTheory

namespace MDPFinance.POMDP

/-- Theorem 5.3.2 (Bäuerle–Rieder, p. 157, PDF 171). Let `π ∈ Π_N`. Then for all `x ∈ E_X`:
`J_N^π(x) = J_N'^π(x,Q_0)` and hence `J_N(x) = J_N'(x,Q_0)`, in `[-∞,∞]`, under the section's
standing Integrability Assumption (p. 151). -/
theorem theorem_5_3_2 {EX EY A : Type*} [MeasurableSpace EX] [MeasurableSpace EY]
    [MeasurableSpace A] [Nonempty A] (M : PartiallyObservableMDM EX EY A) (Fd : FilterData M)
    (M' : FilteredModel M Fd) (N : ℕ) (hInt : M.IntegrabilityAssumption N)
    (π : Policy EX A) (hπ : M.IsPolicy N π) (x : EX) :
    M.JNpi π N x = FilteredModel.JprimeNpi M Fd M' π N x ⟨M.Q0, M.isProbQ0⟩ ∧
      M.JN N x = FilteredModel.Jprime M Fd M' N x ⟨M.Q0, M.isProbQ0⟩ := by sorry

end MDPFinance.POMDP
