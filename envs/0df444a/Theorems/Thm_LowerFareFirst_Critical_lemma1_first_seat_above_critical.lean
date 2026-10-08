-- Prove2me | Theorems.Thm_LowerFareFirst_Critical_lemma1_first_seat_above_critical
-- name    : LowerFareFirst.Critical.lemma1_first_seat_above_critical
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:50.137984+00:00
-- url     : https://prove2.me/theorems/47ab8571-1f42-443e-b434-a28eb7b54ffd
-- title:
--   Lemma 1, p. 29 — Z_{m̄+1}(k_{m̄+1}+1) = Z_{m̄+1}(k_{m̄+1}) + ΔZ_m̄(k_{m̄+1}+1)P[D_{m̄+1}=0] + r_{m̄+1}P[D_{m̄+1} ≥ 1], and ΔZ_{m̄+1} drops there
-- statement:
--   Consider the seat management model with lower fare classes booking first under the standing assumptions of §1, with optimal values $Z_m(n)$, marginal seat values $\Delta Z_m(n) = Z_m(n) - Z_m(n-1)$ and critical values $k_m$ from (2b). Let $\bar m$ be a class with $1 \le \bar m$ and $\bar m + 1 \le c$, suppose that $\Delta Z_{\bar m}(n)$ is decreasing (nonincreasing) in $n \ge 1$, and let $k_{\bar m+1}$ be the critical value of class $\bar m + 1$. Then
--   $$Z_{\bar m+1}(k_{\bar m+1}+1) = Z_{\bar m+1}(k_{\bar m+1}) + \Delta Z_{\bar m}(k_{\bar m+1}+1)\,P[D_{\bar m+1} = 0] + r_{\bar m+1}\,P[D_{\bar m+1} \ge 1]$$
--   and
--   $$\Delta Z_{\bar m+1}(k_{\bar m+1}+1) < \Delta Z_{\bar m+1}(k_{\bar m+1}).$$
--
--   The lemma treats the first seat above the critical value, where class $\bar m + 1$ starts to be accepted: it is the case $j = 1$ of (6) for class $\bar m + 1$, and it shows that the marginal seat value of class $\bar m + 1$ strictly drops at the threshold. Together with Theorem 1 it carries the induction of Theorem 2 from $\bar m$ to $\bar m + 1$.
--
--   **Formalization Note.** The existence of $k_{\bar m+1}$ is a hypothesis, as on the page; it forces $k_{\bar m+1} \ge 1$, so $\Delta Z_{\bar m+1}(k_{\bar m+1})$ is defined. The paper's proof writes $k_{\bar m}$ in three places where $k_{\bar m+1}$ is meant; the statement itself has no slip.
-- source:
--   Wollmer (1992), Operations Research 40(1), Lemma 1, p. 29

import Mathlib
import Definitions.Def_LowerFareFirst_Critical_Model

namespace LowerFareFirst.Critical

open MeasureTheory

theorem lemma1_first_seat_above_critical {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : ℕ → Ω → ℕ) (r : ℕ → ℝ) (c : ℕ)
    (hM : IsSeatModel μ D r c)
    (m k : ℕ) (hm : 1 ≤ m) (hmc : m + 1 ≤ c)
    (hdec : ∀ n : ℕ, 1 ≤ n → dZ μ D r m (n + 1) ≤ dZ μ D r m n)
    (hk : IsCriticalValue μ D r (m + 1) k) :
    Z μ D r (m + 1) (k + 1) =
        Z μ D r (m + 1) k + dZ μ D r m (k + 1) * probEq μ D (m + 1) 0
          + r (m + 1) * probGe μ D (m + 1) 1 ∧
      dZ μ D r (m + 1) (k + 1) < dZ μ D r (m + 1) k := by sorry

end LowerFareFirst.Critical
