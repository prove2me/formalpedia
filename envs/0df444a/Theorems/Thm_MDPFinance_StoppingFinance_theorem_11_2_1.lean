-- Prove2me | Theorems.Thm_MDPFinance_StoppingFinance_theorem_11_2_1
-- name    : MDPFinance.StoppingFinance.theorem_11_2_1
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T23:49:25.405262+00:00
-- url     : https://prove2.me/theorems/34b0e58b-a7ea-4f74-8e02-98e5a1bad554
-- title:
--   Theorem 11.2.1 — the credit granting model: monotonicity and threshold structure
-- statement:
--   For the credit granting model it holds:
--
--   a) $J_n(x)$ is increasing in $x$ and $n$.
--   b) There exist thresholds $x_N^* \le \dots \le x_1^*$ such that the set of states in which the
--      credit is cancelled is given by $S_n^* := \{x \in E \mid x < x_n^*\}$. The optimal credit
--      policy $(f_N^*,\dots,f_1^*)$ is defined by $f_n^* := 1_{S_n^*}$.
--
--   The bank cancels exactly when the borrower's rating falls below a threshold, and that threshold
--   **rises** as the remaining duration shortens: with less time left, a marginal borrower is no
--   longer worth keeping.
--
--   The two structural assumptions are what buy it and neither is cosmetic: $x \mapsto c(x)$
--   increasing, and $Q^X$ stochastically monotone. Without the second, a) fails and with it the
--   threshold structure.
--
--   The proof gives the thresholds explicitly:
--
--   $$ x_n^* := \inf\Big\{x \in E \ \Big|\ c(x) + \beta \int J_{n-1}(x')Q^X(dx'|x) \ge 0\Big\} $$
--
--   with $\inf \emptyset = \infty$, the set being an up-set because the map inside is increasing by
--   a). That $n \mapsto x_n^*$ is decreasing is again obtained from part a).
--
--   The indexing is the book's and runs **backwards**: $x_N^*$ is the threshold with $N$ periods still
--   to run and $x_1^*$ the one with a single period left, so $x_N^* \le \dots \le x_1^*$ says the
--   threshold rises as the horizon shortens.
--
--   These thresholds are the **credit-cancellation boundary**, a different object from Proposition
--   11.1.2's option exercise boundary despite the shared notation $x_n^*$.
--
--   **Moderation note.** The draft's cancellation set was `{J_n = 0}`, which also contains the boundary states where extending and cancelling tie (`c̄_n(x) = 0`), whereas the book's `S_n^* = {x < x_n^*}` with `x_n^* = inf{c̄_n ≥ 0}` continues there — the draft's equivalence `J_n(x) = 0 ↔ x < x_n^*` is false at such states; and `inf ∅ = ∞` was not expressible with real thresholds. Now `S_n^* = {c̄_n < 0} = {x < x_n^*}` with `x_n^* ∈ [-∞,∞]`, and the optimality of `f_n^* = 1_{S_n^*}` is stated as `T_{f_n^*} J_{n−1} = J_n`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, pp. 340-341 (PDF 348-349), Theorem 11.2.1

import Mathlib
import Definitions.Def_MDPFinance_StoppingFinance_CreditModel

open MeasureTheory

namespace MDPFinance.StoppingFinance

/-- **Theorem 11.2.1** (pp. 340-341). Under the structural assumptions: a) `J_n(x)` is increasing
in `x` and in `n`; b) there are thresholds `x_N^* ≤ … ≤ x_1^*` (in `[-∞,∞]`, `inf ∅ = ∞`) such
that the cancellation set with `n` periods left is `S_n^* = {x ∈ E | x < x_n^*}` — the states where
extending, `c̄_n(x) = c(x) + β ∫ J_{n−1} dQ^X(·|x)`, is worse than cancelling — and the policy
`f_n^* := 1_{S_n^*}` is optimal: `f_n^*` is a maximizer of `J_{n-1}` (`T_{f_n^*} J_{n−1} = J_n`). -/
theorem theorem_11_2_1 (M : CreditModel) (hM : M.StructuralAssumptions) (N : ℕ) :
    (∀ n : ℕ, Monotone (M.J n)) ∧
    (∀ (m n : ℕ), m ≤ n → ∀ x : ℝ, M.J m x ≤ M.J n x) ∧
    (∃ xstar : ℕ → EReal,
      (∀ (m n : ℕ), 1 ≤ m → m ≤ n → n ≤ N → xstar n ≤ xstar m) ∧
      (∀ (n : ℕ) (x : ℝ), 1 ≤ n → n ≤ N → (M.cbar n x < 0 ↔ (x : EReal) < xstar n)) ∧
      ∀ (n : ℕ) (x : ℝ), 1 ≤ n → n ≤ N →
        (if (x : EReal) < xstar n then 0 else M.cbar n x) = M.J n x) := by sorry

end MDPFinance.StoppingFinance
