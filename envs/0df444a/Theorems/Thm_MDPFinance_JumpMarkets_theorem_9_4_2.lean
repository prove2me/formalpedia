-- Prove2me | Theorems.Thm_MDPFinance_JumpMarkets_theorem_9_4_2
-- name    : MDPFinance.JumpMarkets.theorem_9_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:28:40.436124+00:00
-- url     : https://prove2.me/theorems/e8db1627-a7fb-4ecb-aa43-b4ae3bca46fa
-- title:
--   Theorem 9.4.2 — the optimal execution rate is monotone and unit-Lipschitz in the inventory
-- statement:
--   **Theorem 9.4.2** (p. 296).
--
--   a) The value function $V(t,x)$ is the unique fixed point of $\mathcal{T}$ in $IM_{cx}$.
--   b) There exists an optimal Markov strategy $\pi^* = (\pi^*_t)$ such that
--      $\pi^*_t = f^*(t, X_{t-})$ and $f^*$ satisfies $f^*(t,x) \le f^*(t,x+1) \le f^*(t,x) + 1$, and
--      $(X_t)$ is the corresponding number of share process.
--
--   The structural answer to the execution problem: sell more when you hold more, but never more than
--   one extra share per extra share held. Both inequalities are the theorem.
--
--   **$f^*(t,x) \le f^*(t,x+1)$ alone would be a generic monotonicity claim.** It is the upper bound
--   $f^*(t,x+1) \le f^*(t,x)+1$ that carries the content — the optimal block size is **unit-Lipschitz**
--   in the inventory, so the execution schedule cannot jump. Dropping it loses half the theorem, and it
--   is the half that takes the work: the book proves it by contradiction from the strict convexity
--   **(9.19)** of $C$.
--
--   **$IM_{cx}$, not $IM_{cv}$.** This is a minimisation with a convex cost and a convex value
--   function, the opposite curvature from §9.3's terminal wealth problem; the two sets are not
--   interchangeable.
--
--   $f^*$ is the **smallest** minimizer of $C(u) + v(t,x-u)$ over $u \in \{0,\dots,x\}$ **(9.22)**,
--   the book's own choice; with an arbitrary selection of minimizers the unit-Lipschitz bound need not
--   hold.
--
--   Optimality is stated at the level of the discrete-time model, where $\mathcal{T}$ lives: $f^*$
--   minimizes the operator's argument at the value function, so the stationary policy is optimal for
--   the discrete-time model, and — by Theorem 8.3.2, which p. 295 invokes and which belongs to chunk
--   `08` — that determines an optimal control process for the continuous-time problem. The inner
--   optimisation is over a **finite** set, so no `sSup`/`sInf` junk-value device is needed here,
--   unlike in §9.3.
--
--   **Moderation note.** The draft assumed `V` to be *some* fixed point of `𝒯` in `IM_cx` and concluded its uniqueness, never connecting it to the value function; b)'s optimal strategy was absent (only the minimizer property of `f^*`). Now a) is: the value function `V` of the embedded model lies in `IM_cx`, is a fixed point of `𝒯`, and is the only one there; b) `f^* = f^*_V` is monotone and unit-Lipschitz in `x`, and there is an admissible measurable policy `f(t,x)(s) = f^*(t+s,x)` attaining `V` (the strategy `π^*_t = f^*(t, X_{t-})`).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 296 (PDF 306), Theorem 9.4.2

import Mathlib
import Definitions.Def_MDPFinance_JumpMarkets_TradeExecution

open MeasureTheory
open scoped ENNReal

namespace MDPFinance.JumpMarkets

/-- **Theorem 9.4.2** (p. 296). a) The value function `V(t,x)` is the unique fixed point of
`𝒯` in `IM_cx`. b) There is an optimal Markov strategy `π^*_t = f^*(t, X_{t-})` — the policy
`f(t,x)(s) := f^*(t+s, x)` of the embedded model attains `V` — where `f^*` is the smallest
minimizer **(9.22)** at `V`, and `f^*(t,x) ≤ f^*(t,x+1) ≤ f^*(t,x) + 1`. -/
theorem theorem_9_4_2 (M : TradeExecution) :
    ∃ V : ℝ × ℕ → ℝ, M.IMcx V ∧
      (∀ p ∈ M.E, M.Jinf p = ENNReal.ofReal (V p)) ∧
      (∀ p ∈ M.E, M.T_op V p = V p) ∧
      (∀ v : ℝ × ℕ → ℝ, M.IMcx v → (∀ p ∈ M.E, M.T_op v p = v p) → ∀ p ∈ M.E, v p = V p) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ x : ℕ,
        M.fstar V (t, x) ≤ M.fstar V (t, x + 1) ∧
        M.fstar V (t, x + 1) ≤ M.fstar V (t, x) + 1) ∧
      (∃ f : ℕ → ℝ × ℕ → Offer, TradeExecution.IsPolicy f ∧
        (∀ n, ∀ p ∈ M.E, ∀ s : ℝ, 0 ≤ s → (f n p).val s = M.fstar V (p.1 + s, p.2)) ∧
        ∀ p ∈ M.E, M.Jinfpi f p = M.Jinf p) := by sorry

end MDPFinance.JumpMarkets
