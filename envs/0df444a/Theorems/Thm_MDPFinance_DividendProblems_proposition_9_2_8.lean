-- Prove2me | Theorems.Thm_MDPFinance_DividendProblems_proposition_9_2_8
-- name    : MDPFinance.DividendProblems.proposition_9_2_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:13:28.641475+00:00
-- url     : https://prove2.me/theorems/212491d0-6b7d-436e-8065-3b571effbcb7
-- title:
--   Proposition 9.2.8 — the increment property below ξ
-- statement:
--   Below $\xi$, the optimal dividend amount can only increase by exactly $1$ from one state to the next, whenever it increases at all: if $f^*(x_0)=a_0$ and $f^*(x_0+1)>0$, then $f^*(x_0+1)=a_0+1$. This rules out the optimal payout jumping by more than one unit as the reserve increases by one, and is exactly the fact that forces the "pay down to a fixed threshold" bands of the goal's band-policy structure, rather than some more erratic payout pattern.
--
--   **Moderation note.** Unchanged in form; now about the corrected `J_∞`/largest maximizer.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 277, PDF 287, Proposition 9.2.8

import Mathlib
import Definitions.Def_MDPFinance_DividendProblems_MDM
import Definitions.Def_MDPFinance_DividendProblems_Dividend

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace MDPFinance.DividendProblems

/-- Proposition 9.2.8 (Bäuerle–Rieder, p. 277, PDF 287). Let `x_0 \ge 0`. If `f^*(x_0) = a_0` and
`f^*(x_0+1) > 0`, then `f^*(x_0+1) = a_0 + 1`. -/
theorem proposition_9_2_8 (M : DividendModel) (fstar : ℤ → ℕ) (hfstar : M.IsLargestMaximizer fstar)
    (x0 : ℤ) (hx0 : 0 ≤ x0) (a0 : ℕ) (ha0 : fstar x0 = a0) (hpos : 0 < fstar (x0 + 1)) :
    fstar (x0 + 1) = a0 + 1 := by sorry

end MDPFinance.DividendProblems
