-- Prove2me | Theorems.Thm_MarketplaceSharing_Threshold_theorem_1
-- name    : MarketplaceSharing.Threshold.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:32:30.074864+00:00
-- url     : https://prove2.me/theorems/4b7bbab0-7d42-423d-8e46-eabf08dcd211
-- title:
--   Theorem 1, p. 9 — ΔVₙ increases in time-to-go, sharing unit n is optimal iff t ≤ tₙ, and Vₙ has the form (4) on [tⱼ₋₁, tⱼ] (exponents with r)
-- statement:
--   Let $(V_n)_{n\ge0}$ be the revenue-to-go of the inventory sharing model with price $\pi$, commission $\theta\in[0,1]$, arrival rates $\lambda_D, \lambda_P > 0$ and discount rate $r \ge 0$ — a solution of the HJB system (3) with $V_0 \equiv 0$ and $V_n(0) = 0$. Let $\Delta V_n(t) = V_n(t) - V_{n-1}(t)$, $t_0 = 0$, and
--   $$t_n = \sup\{t \ge 0 : \Delta V_n(t) \le (1-\theta)\pi\} \in [0,\infty] \quad (n \ge 1).$$
--   Then for every $n \ge 1$:
--   1. $\Delta V_n$ is strictly increasing on $[0,\infty)$, and for $t \ge 0$, $\Delta V_n(t) = (1-\theta)\pi$ if and only if $t = t_n$;
--   2. for $t \ge 0$, sharing unit $n$ is optimal (attains the supremum in (3)) if and only if $t \le t_n$, and for $t > t_n$ not sharing is optimal and sharing is not;
--   3. on each interval $I_{nj} = [t_{j-1}, t_j]$, $j \in \{1,\dots,n\}$, and on $I_{n,n+1} = [t_n, \infty)$, there are constants $C_{nj}$, $A_{nji}$, $B_{nji}$ with
--   $$V_n(t) = C_{nj} + \sum_{i=0}^{n-j} A_{nji}\, t^i e^{-(\lambda_D+\lambda_P+r)t} + \sum_{i=0}^{j-2} B_{nji}\, t^i e^{-(\lambda_D+r)t}, \qquad t \in I_{nj}.$$
--
--   The theorem characterizes the optimal sharing policy completely — a time threshold per unit — and gives the revenue-to-go in closed form between consecutive thresholds.
--
--   **Formalization Note.** The printed (4) has exponents $\lambda_D + \lambda_P$ and $\lambda_D$; with discounting the proof on p. 30 carries $r$ (e.g. $A_{110}e^{-(\lambda+r)t}$), and the printed form is exact only at $r = 0$. When some $t_j = \infty$ the later intervals are empty and clause 3 holds there trivially, as in the paper. "There is an unique $t_n$" is read with p. 10's convention $t_n = \infty$ when $\Delta V_n = (1-\theta)\pi$ has no solution. The coefficients are existential ("can be written as"); their recursions are not part of the statement. $n$ ranges over $n \ge 1$.
-- source:
--   Martínez-de-Albéniz, Pinto & Amorim, Driving Supply to Marketplaces, SSRN 3643261 (June 30, 2020), p. 9, Theorem 1 (both bullets, eq. (4)); p. 10 (tₙ = ∞ convention); Appendix p. 30 (exponents with r)

import Mathlib
import Definitions.Def_MarketplaceSharing_Threshold_Model

namespace MarketplaceSharing.Threshold
theorem theorem_1 (p : Params) (V : ℕ → ℝ → ℝ) (hV : p.IsRevenueToGo V) :
    ∀ n : ℕ, 1 ≤ n →
      (StrictMonoOn (marginal V n) (Set.Ici 0) ∧
      (∀ t : ℝ, 0 ≤ t → (marginal V n t = p.platformMargin ↔ (t : EReal) = p.threshold V n)) ∧
      (∀ t : ℝ, 0 ≤ t → (p.IsOptimalDecision V n t true ↔ (t : EReal) ≤ p.threshold V n)) ∧
      (∀ t : ℝ, 0 ≤ t → p.threshold V n < (t : EReal) →
        p.IsOptimalDecision V n t false ∧ ¬ p.IsOptimalDecision V n t true)) ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ n + 1 →
        ClosedFormOn p (V n) n j
          {t : ℝ | 0 ≤ t ∧ p.threshold V (j - 1) ≤ (t : EReal) ∧
            (j ≤ n → (t : EReal) ≤ p.threshold V j)} := by sorry
end MarketplaceSharing.Threshold
