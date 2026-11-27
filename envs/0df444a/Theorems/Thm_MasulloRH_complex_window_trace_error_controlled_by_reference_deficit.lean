-- Prove2me | Theorems.Thm_MasulloRH_complex_window_trace_error_controlled_by_reference_deficit
-- name    : MasulloRH.complex_window_trace_error_controlled_by_reference_deficit
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T03:24:02.401502+00:00
-- url     : https://prove2.me/theorems/0efdf6bb-3c65-5e22-9f8a-e102dee33f81
-- title:
--   The real reference deficit controls complex Masullo trace errors
-- statement:
--   Let W be the sum of the multiplicity-weighted inverse quadratic height weights of zeros omitted by a window of half-width α. At s=3 the full real trace minus the narrow real trace lies between W/4 and W/2. At every complex s with Re(s)>1, the norm difference of the two traces is bounded by W times d(1+d/(Re(s)-1)), where d is the distance to 5/2. The claims hold for every real width, including widths passing through a zero.
-- source:
--   Masullo, The Music of the Primes, §§1.4.2–1.4.5 and Theorem 12.5.1.1. These estimates concern the regularized trace windows in the Masullo mission and the compensated resolvent at reference exponent 5/2. The existing low/high split is https://prove2.me/theorems/1b39c093-ef5a-4b28-95db-9cc637c7997c. Uses the published reference-resolvent sandwich and summability of the zero decay weights.

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

open MasulloRH ArithmeticFunction

theorem MasulloRH.complex_window_trace_error_controlled_by_reference_deficit (α : ℝ) (s : ℂ) (hs : 1 < s.re) :
    let W := ∑' z : ZetaZerosInTraceStrip (1 / 2),
      if α ≤ |z.val.re - 1 / 2| then zeroDecayWeight (1 / 2) z else 0
    let D := (regularizedTraceRHS (1 / 2) 3).re - (regularizedTraceRHS α 3).re
    W / 4 ≤ D ∧ D ≤ W / 2 ∧
      ‖regularizedTraceRHS (1 / 2) s - regularizedTraceRHS α s‖ ≤
        ‖s - 5 / 2‖ * (1 + ‖s - 5 / 2‖ / (s.re - 1)) * W := by sorry
