-- Prove2me | Theorems.Thm_LowerFareFirst_Critical_note2b_critical_sign
-- name    : LowerFareFirst.Critical.note2b_critical_sign
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:17.598801+00:00
-- url     : https://prove2.me/theorems/56a3cd4b-e8ae-4c6e-ae89-7f0328e343e2
-- title:
--   Note after (2b), p. 28 — if ΔZ_{m−1} is decreasing, r_m < ΔZ_{m−1}(n) for n ≤ k_m and r_m ≥ ΔZ_{m−1}(n) for n ≥ k_m + 1
-- statement:
--   Let $(\Omega, \mu)$ carry integer-valued demands $D_m$, let $r_m$ be fares, and let $Z_m(n)$, $\Delta Z_m(n) = Z_m(n) - Z_m(n-1)$ be the optimal values and marginal seat values of the seat management model with lower classes booking first. Fix a class $m \ge 2$ and suppose that $\Delta Z_{m-1}(n)$ is decreasing (nonincreasing) in $n \ge 1$. Let $k$ be the critical value of class $m$,
--   $$k = k_m = \max\{\, n \ge 1 \mid r_m < \Delta Z_{m-1}(n) \,\}.$$
--   Then
--   $$r_m < \Delta Z_{m-1}(n) \quad \text{for } 1 \le n \le k_m, \qquad r_m \ge \Delta Z_{m-1}(n) \quad \text{for } n \ge k_m + 1.$$
--
--   So the fare of class $m$ falls below the expected value of the marginal seat to the higher classes exactly when at most $k_m$ seats remain; this is why a class-$m$ request should be rejected if and only if $n \le k_m$. For $m = 2$ this is the paper's condition (5), with $\Delta Z_1(n) = r_1 P[D_1 \ge n]$.
--
--   **Formalization Note.** The paper's hypothesis "$\Delta Z_m(n)$ is decreasing in $n$ for all $m$" is used only for class $m - 1$, and is stated only there; none of the standing assumptions of §1 is needed. Both changes make the statement more general. The existence of $k_m$ is taken as a hypothesis, as on the page.
-- source:
--   Wollmer (1992), Operations Research 40(1), §1, paragraph after Eq. (2b), p. 28; with Eq. (5), §2, p. 28

import Mathlib
import Definitions.Def_LowerFareFirst_Critical_Model

namespace LowerFareFirst.Critical

open MeasureTheory

theorem note2b_critical_sign {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : ℕ → Ω → ℕ) (r : ℕ → ℝ) (m k : ℕ) (hm : 2 ≤ m)
    (hdec : ∀ n : ℕ, 1 ≤ n → dZ μ D r (m - 1) (n + 1) ≤ dZ μ D r (m - 1) n)
    (hk : IsCriticalValue μ D r m k) :
    (∀ n : ℕ, 1 ≤ n → n ≤ k → r m < dZ μ D r (m - 1) n) ∧
      (∀ n : ℕ, k + 1 ≤ n → dZ μ D r (m - 1) n ≤ r m) := by sorry

end LowerFareFirst.Critical
