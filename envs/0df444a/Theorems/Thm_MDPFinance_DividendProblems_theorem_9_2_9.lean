-- Prove2me | Theorems.Thm_MDPFinance_DividendProblems_theorem_9_2_9
-- name    : MDPFinance.DividendProblems.theorem_9_2_9
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T23:14:10.850443+00:00
-- url     : https://prove2.me/theorems/af548942-bb2c-40db-86e5-a071572be024
-- title:
--   Theorem 9.2.9 — the optimal policy is a band-policy
-- statement:
--   This is the section's payoff and this mission's goal: the stationary policy $(f^*,f^*,\dots)$, $f^*$ the largest maximizer of $J_\infty$, is optimal for the dividend model, and — the deep combinatorial content — has the band-policy structure of Definition 9.2.5: a finite alternation of "pay nothing" and "pay down to a threshold" intervals. The proof (not reproduced here) builds the band structure explicitly by repeatedly applying Propositions 9.2.6 and 9.2.8 downward from $\xi$, splitting into cases at each point where $f^*$ returns to $0$.
--
--   **Formalization Note.** The conclusion is stated as the *general* band-policy property, not the barrier-policy special case (which is Theorem 9.2.10 b)'s strictly narrower, conditionally-true conclusion): stating this goal with a barrier-policy conclusion instead would understate the theorem, exactly the chapter-specific pitfall this mission's `BRIEF.md` warns against.
--
--   **Moderation note.** Unchanged in form; optimality is `J_{∞(f^*)^∞} = J_∞` in `[0,∞]` over `F^∞`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 278, PDF 288, Theorem 9.2.9

import Mathlib
import Definitions.Def_MDPFinance_DividendProblems_MDM
import Definitions.Def_MDPFinance_DividendProblems_Dividend
import Definitions.Def_MDPFinance_DividendProblems_BandPolicy

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace MDPFinance.DividendProblems

/-- Theorem 9.2.9 (Bäuerle–Rieder, p. 278, PDF 288). The stationary policy `(f^*,f^*,\dots)`,
`f^*` the largest maximizer of `J_\infty`, is optimal (`J_{\infty (f^*)^\infty} = J_\infty`) and
is a band-policy (Definition 9.2.5, on the nonnegative states; `f^*(x) = 0` for `x < 0` is
forced by `D(x) = \{0\}`). -/
theorem theorem_9_2_9 (M : DividendModel) (fstar : ℤ → ℕ) (hfstar : M.IsLargestMaximizer fstar) :
    (∀ x : ℤ, Jinfpi M.toMDM (fun _ => fstar) x = M.Jinf x) ∧
      IsBandPolicy (fun x : ℕ => fstar (x : ℤ)) := by sorry

end MDPFinance.DividendProblems
