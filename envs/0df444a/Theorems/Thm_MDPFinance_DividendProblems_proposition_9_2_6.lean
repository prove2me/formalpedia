-- Prove2me | Theorems.Thm_MDPFinance_DividendProblems_proposition_9_2_6
-- name    : MDPFinance.DividendProblems.proposition_9_2_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:13:21.529276+00:00
-- url     : https://prove2.me/theorems/f0b8de21-5699-4a8b-a3b8-f8c5da49993e
-- title:
--   Proposition 9.2.6 — the finite top threshold ξ
-- statement:
--   $\xi := \sup\{x \in \mathbb N_0 \mid f^*(x)=0\}$, the largest state at which the optimal policy pays nothing, is shown to be **finite** — not assumed — via the explicit bound Theorem 9.2.3's inequalities force on any such $x$, and $f^*(x)=x-\xi$ for every $x\ge\xi$: above $\xi$, the optimal policy is a simple barrier at $\xi$. This is the first genuinely structural fact about $f^*$'s shape, and the anchor the whole band-policy structure is built around.
--
--   **Moderation note.** The draft's `(n = 0 ∨ f^*(n) = 0)` disjunct weakened `ξ` to an upper bound of the set of zeros; since `f^*(0) = 0` (`D(0) = {0}`), `ξ < ∞` says the set has a maximum, now stated as `f^*(n) = 0 ∧ ∀ x, f^*(x) = 0 → x ≤ n`, with `f^*(x) = x − n` for `x ≥ n`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 276, PDF 286, Proposition 9.2.6

import Mathlib
import Definitions.Def_MDPFinance_DividendProblems_MDM
import Definitions.Def_MDPFinance_DividendProblems_Dividend

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace MDPFinance.DividendProblems

/-- Proposition 9.2.6 (Bäuerle–Rieder, p. 276, PDF 286). `\xi := \sup\{x \in \mathbb N_0 \mid
f^*(x) = 0\}` is finite and `f^*(x) = x - \xi` for all `x \ge \xi`. The set contains `0`
(`D(0) = \{0\}`), so "`\xi < \infty`" says it has a maximum `n`: `f^*(n) = 0` and every `x` with
`f^*(x) = 0` satisfies `x \le n`. -/
theorem proposition_9_2_6 (M : DividendModel) (fstar : ℤ → ℕ) (hfstar : M.IsLargestMaximizer fstar) :
    ∃ n : ℕ, fstar (n : ℤ) = 0 ∧ (∀ x : ℕ, fstar (x : ℤ) = 0 → x ≤ n) ∧
      ∀ x : ℤ, (n : ℤ) ≤ x → fstar x = (x - n).toNat := by sorry

end MDPFinance.DividendProblems
