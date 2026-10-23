-- Prove2me | Theorems.Thm_MarketplaceSharing_Threshold_theorem_1_first_bullet
-- name    : MarketplaceSharing.Threshold.theorem_1_first_bullet
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:32:24.507927+00:00
-- url     : https://prove2.me/theorems/cb7101e9-234f-4427-a9a2-d0a00bf7078e
-- title:
--   Theorem 1 (first bullet), p. 9 — ΔVₙ strictly increases in time-to-go; ΔVₙ = (1 − θ)π exactly at tₙ ∈ [0, ∞]; sharing unit n is optimal iff t ≤ tₙ
-- statement:
--   Let $(V_n)_{n\ge0}$ be the revenue-to-go of the inventory sharing model (a solution of the HJB system (3) with $V_0 \equiv 0$ and $V_n(0) = 0$), $\Delta V_n(t) = V_n(t) - V_{n-1}(t)$, and
--   $$t_n = \sup\{t \ge 0 : \Delta V_n(t) \le (1-\theta)\pi\} \in [0,\infty].$$
--   Then for every $n \ge 1$:
--   1. $\Delta V_n$ is strictly increasing on $[0, \infty)$;
--   2. for $t \ge 0$, $\Delta V_n(t) = (1-\theta)\pi$ if and only if $t = t_n$ (so there is no solution when $t_n = \infty$);
--   3. for $t \ge 0$, sharing ($z = 1$) attains the supremum in (3) if and only if $t \le t_n$;
--   4. for $t > t_n$, not sharing ($z = 0$) attains the supremum in (3) and sharing does not.
--
--   This is the threshold structure of the optimal policy: the supplier keeps its $n$-th unit to its own store early in the season and shares it with the platform once the time-to-go falls to $t_n$.
--
--   **Formalization Note.** "Optimal" means attaining the supremum of the bracket in (3), the paper's own reading on p. 8. At $t = t_n$ both decisions are optimal and the paper breaks the tie towards sharing; clauses 3 and 4 together say exactly that. The paper's "there is an unique $t_n$" fails when $\Delta V_n$ stays below $(1-\theta)\pi$ (e.g. $\theta = 0$); clause 2 then holds with $t_n = \infty$, p. 10's convention.
-- source:
--   Martínez-de-Albéniz, Pinto & Amorim, Driving Supply to Marketplaces, SSRN 3643261 (June 30, 2020), p. 9, Theorem 1, first bullet; p. 10 (tₙ = ∞ convention)

import Mathlib
import Definitions.Def_MarketplaceSharing_Threshold_Model

namespace MarketplaceSharing.Threshold
theorem theorem_1_first_bullet (p : Params) (V : ℕ → ℝ → ℝ) (hV : p.IsRevenueToGo V) :
    ∀ n : ℕ, 1 ≤ n →
      StrictMonoOn (marginal V n) (Set.Ici 0) ∧
      (∀ t : ℝ, 0 ≤ t → (marginal V n t = p.platformMargin ↔ (t : EReal) = p.threshold V n)) ∧
      (∀ t : ℝ, 0 ≤ t → (p.IsOptimalDecision V n t true ↔ (t : EReal) ≤ p.threshold V n)) ∧
      (∀ t : ℝ, 0 ≤ t → p.threshold V n < (t : EReal) →
        p.IsOptimalDecision V n t false ∧ ¬ p.IsOptimalDecision V n t true) := by sorry
end MarketplaceSharing.Threshold
