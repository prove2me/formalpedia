-- Prove2me | Theorems.Thm_LostSalesOldNew_LeadTime_optimality_equation
-- name    : LostSalesOldNew.LeadTime.optimality_equation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:25:43.089912+00:00
-- url     : https://prove2.me/theorems/844b5822-0361-4d15-9335-d97c4eb912ba
-- title:
--   (3), p. 1257 — f* satisfies f(x) = min_{z≥0}{q(x,z) + γE[f(x_+)]}, the minimum is attained, and f* is the least solution
-- statement:
--   Consider the lost-sales system of Zipkin (2008), §2, with lead time $L \ge 1$, cost data $c,\hat h,p \ge 0$, discount factor $\gamma \in [0,1)$, and i.i.d. demand with law $D$ on $[0,\infty)$ with finite mean. Let $f^{*L}$ be the infinite-horizon optimal cost, the limit of the finite-horizon optimal costs of recursion (2) as the horizon grows, let $q(x,z) = q^L(x,z)$ be the transformed one-period cost and $x_+ = ([x_0-d]^+ + x_1, x_2, \dots, x_{L-1}, z)$ the next state. Then:
--
--   1. for every state $x \ge 0$,
--   $$f^{*L}(x) = \inf_{z \ge 0}\Bigl\{ q(x,z) + \gamma\, E\bigl[f^{*L}(x_+)\bigr] \Bigr\};$$
--   2. if $c > 0$ or $\hat h > 0$, the infimum is a minimum: for every $x \ge 0$ there is an order $z^*(x) \ge 0$ with $f^{*L}(x) = q(x,z^*(x)) + \gamma E[f^{*L}(x_+)]$, the next state taken with $z = z^*(x)$;
--   3. $f^{*L}$ is the least solution: every function $g$ with values in $[0,\infty]$ that satisfies the equation of item 1 at every $x \ge 0$ satisfies $f^{*L}(x) \le g(x)$ for every $x \ge 0$.
--
--   This is the functional equation (3) of the paper: the optimal cost of the infinite-horizon problem satisfies the Bellman equation with a minimizing order, and it is singled out among the solutions. The lead-time bound (6) is obtained by substituting into it.
--
--   **Formalization Note.** The paper says the optimal cost "uniquely satisfies" (3), calls $f^*$ "the solution" and $z^*(x)$ "an optimal policy", without naming a function class for uniqueness. Uniqueness in an unspecified class is not formalized; item 3 states the class-free part of it, that $f^{*L}$ is the least nonnegative solution. Attainment (item 2) is stated under $c > 0$ or $\hat h > 0$: when $c = \hat h = 0$ and demand has unbounded support, $f^{*L} \equiv 0$ but every order leaves a positive expected penalty, so the paper's $\min$ is not attained in that degenerate case. The optimal cost is defined as $\sup_n T^n 0$ (value iteration from the terminal condition $f_{T+1} = 0$ of (2)), with values in $[0,\infty]$. The equation is stated at nonnegative states, the states the system visits.
-- source:
--   Zipkin, Old and New Methods for Lost-Sales Inventory Systems, Operations Research 56(5) (2008), (3), p. 1257

import Mathlib
import Definitions.Def_LostSalesOldNew_LeadTime_Model

namespace LostSalesOldNew.LeadTime

open MeasureTheory

theorem optimality_equation (K : Costs) (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD : LostSalesOldNew.StateReduction.IsDemand D) (hmean : Integrable (fun d : ℝ => d) D)
    (L : ℕ) (hL : 1 ≤ L) :
    (∀ x : Fin L → ℝ, (∀ i, 0 ≤ x i) → fStar K D L x = bellman K D L (fStar K D L) x) ∧
    ((0 < K.c ∨ 0 < K.hhat) → ∀ x : Fin L → ℝ, (∀ i, 0 ≤ x i) → ∃ z : ℝ, 0 ≤ z ∧
      fStar K D L x = ENNReal.ofReal (qL K D L (Fin.snoc (α := fun _ => ℝ) x z))
        + ENNReal.ofReal K.γ * ∫⁻ d, fStar K D L (LostSalesOldNew.StateReduction.next x z d) ∂D) ∧
    (∀ g : (Fin L → ℝ) → ENNReal,
      (∀ x : Fin L → ℝ, (∀ i, 0 ≤ x i) → g x = bellman K D L g x) →
      ∀ x : Fin L → ℝ, (∀ i, 0 ≤ x i) → fStar K D L x ≤ g x) := by sorry

end LostSalesOldNew.LeadTime
