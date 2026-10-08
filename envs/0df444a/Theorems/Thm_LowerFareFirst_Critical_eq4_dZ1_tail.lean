-- Prove2me | Theorems.Thm_LowerFareFirst_Critical_eq4_dZ1_tail
-- name    : LowerFareFirst.Critical.eq4_dZ1_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:24.696997+00:00
-- url     : https://prove2.me/theorems/ff28a1bf-30bb-4724-94d2-8989cdc7c3b1
-- title:
--   Eq. (4), p. 28 — ΔZ_1(n) = r_1P[D_1 ≥ n], and ΔZ_1(n) is decreasing in n
-- statement:
--   In the seat management model with lower fare classes booking first (fares $r_1 > \cdots > r_c > 0$, integer-valued demands $D_m$, optimal values $Z_m(n)$, standing assumptions of §1), let $\Delta Z_1(n) = Z_1(n) - Z_1(n-1)$ be the marginal value of the $n$-th seat when only class 1 books.
--
--   For every $n \ge 1$,
--   $$\Delta Z_1(n) = r_1\,P[D_1 \ge n],$$
--   and $\Delta Z_1$ is decreasing (nonincreasing) in $n$: $\Delta Z_1(n+1) \le \Delta Z_1(n)$ for all $n \ge 1$.
--
--   This is the starting point of the induction of Theorem 2, and with (2b) it gives the classical two-class rule (5): a class 2 request is refused exactly when $r_2 < r_1 P[D_1 \ge n]$.
--
--   **Formalization Note.** "Decreasing" is read as nonincreasing: $P[D_1 \ge n]$ is constant on any $n$ with $P[D_1 = n] = 0$, so the strict reading is false.
-- source:
--   Wollmer (1992), Operations Research 40(1), §2, Eq. (4) and the sentence after it, p. 28

import Mathlib
import Definitions.Def_LowerFareFirst_Critical_Model

namespace LowerFareFirst.Critical

open MeasureTheory

theorem eq4_dZ1_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : ℕ → Ω → ℕ) (r : ℕ → ℝ) (c : ℕ)
    (hM : IsSeatModel μ D r c) :
    (∀ n : ℕ, 1 ≤ n → dZ μ D r 1 n = r 1 * probGe μ D 1 n) ∧
      (∀ n : ℕ, 1 ≤ n → dZ μ D r 1 (n + 1) ≤ dZ μ D r 1 n) := by sorry

end LowerFareFirst.Critical
