-- Prove2me | Theorems.Thm_LowerFareFirst_Critical_theorem1_closed_form_and_decreasing
-- name    : LowerFareFirst.Critical.theorem1_closed_form_and_decreasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:35.771496+00:00
-- url     : https://prove2.me/theorems/888c0ecd-51d9-4bf8-be94-9f5cef43432e
-- title:
--   Theorem 1, p. 29 — if ΔZ_m̄ is decreasing, Z_{m̄+1}(k_{m̄+1}+j) satisfies (6) for j ≥ 1 and ΔZ_{m̄+1}(n) decreases for n > k_{m̄+1}+1
-- statement:
--   Consider the seat management model with lower fare classes booking first under the standing assumptions of §1, with optimal values $Z_m(n)$, marginal seat values $\Delta Z_m(n) = Z_m(n) - Z_m(n-1)$ and critical values $k_m$ from (2b). Let $\bar m$ be a class with $1 \le \bar m$ and $\bar m + 1 \le c$, suppose that $\Delta Z_{\bar m}(n)$ is decreasing (nonincreasing) in $n \ge 1$, and write $k = k_{\bar m+1}$ for the critical value of class $\bar m + 1$. Then:
--
--   1. for every $j \ge 1$, $Z_{\bar m+1}(k + j)$ is given by (6) for $m = \bar m + 1$:
--   $$Z_{\bar m+1}(k+j) = Z_{\bar m+1}(k) + \sum_{i=0}^{j-1} \Big\{ \Delta Z_{\bar m}(k+j-i)\,P[D_{\bar m+1} \le i] + r_{\bar m+1}\,P[D_{\bar m+1} \ge i+1] \Big\};$$
--   2. $\Delta Z_{\bar m+1}(n)$ is decreasing in $n$ for $n > k + 1$, that is, $\Delta Z_{\bar m+1}(n+1) \le \Delta Z_{\bar m+1}(n)$ for every $n \ge k + 1$.
--
--   Formula (6) computes the optimal value of classes $1, \dots, \bar m + 1$ above the critical value from the marginal values of classes $1, \dots, \bar m$; it is the basis of the paper's algorithm. Together with Lemma 1 and the equality $Z_{\bar m+1} = Z_{\bar m}$ below $k$, part 2 makes $\Delta Z_{\bar m+1}$ decreasing everywhere, which is the inductive step of Theorem 2.
--
--   **Formalization Note.** "Decreasing" is read as nonincreasing. The existence of $k_{\bar m+1}$ is a hypothesis, as on the page.
-- source:
--   Wollmer (1992), Operations Research 40(1), Theorem 1, p. 29; Eq. (6), p. 28

import Mathlib
import Definitions.Def_LowerFareFirst_Critical_Model

namespace LowerFareFirst.Critical

open MeasureTheory

theorem theorem1_closed_form_and_decreasing {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : ℕ → Ω → ℕ) (r : ℕ → ℝ) (c : ℕ)
    (hM : IsSeatModel μ D r c)
    (m k : ℕ) (hm : 1 ≤ m) (hmc : m + 1 ≤ c)
    (hdec : ∀ n : ℕ, 1 ≤ n → dZ μ D r m (n + 1) ≤ dZ μ D r m n)
    (hk : IsCriticalValue μ D r (m + 1) k) :
    (∀ j : ℕ, 1 ≤ j → Z μ D r (m + 1) (k + j) =
        Z μ D r (m + 1) k + ∑ i ∈ Finset.range j,
          (dZ μ D r m (k + j - i) * probLe μ D (m + 1) i + r (m + 1) * probGe μ D (m + 1) (i + 1))) ∧
      (∀ n : ℕ, k + 1 ≤ n → dZ μ D r (m + 1) (n + 1) ≤ dZ μ D r (m + 1) n) := by sorry

end LowerFareFirst.Critical
