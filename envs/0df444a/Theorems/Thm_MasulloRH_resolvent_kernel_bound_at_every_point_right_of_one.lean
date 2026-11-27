-- Prove2me | Theorems.Thm_MasulloRH_resolvent_kernel_bound_at_every_point_right_of_one
-- name    : MasulloRH.resolvent_kernel_bound_at_every_point_right_of_one
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T03:23:59.640981+00:00
-- url     : https://prove2.me/theorems/188feef1-d436-57db-a230-2c855d0e1409
-- title:
--   An anchored resolvent estimate throughout the half-plane to the right of one
-- statement:
--   For each critical-strip zero and each complex s with real part greater than one, write d for the distance from s to 5/2. The norm of the multiplicity-weighted resolvent term is at most d(1+d/(Re(s)-1)) times the zero decay weight. The bound vanishes at the regularization point.
-- source:
--   Masullo, The Music of the Primes, §§1.4.2–1.4.5 and Theorem 12.5.1.1. These estimates concern the regularized trace windows in the Masullo mission and the compensated resolvent at reference exponent 5/2. The existing low/high split is https://prove2.me/theorems/1b39c093-ef5a-4b28-95db-9cc637c7997c. Original estimate obtained by factoring the difference of the two resolvents.

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

open MasulloRH ArithmeticFunction

theorem MasulloRH.resolvent_kernel_bound_at_every_point_right_of_one (s : ℂ) (hs : 1 < s.re) (z : ZetaZerosInTraceStrip (1 / 2)) :
    ‖zeroResolventTerm (1 / 2) s z‖ ≤
      ‖s - 5 / 2‖ * (1 + ‖s - 5 / 2‖ / (s.re - 1)) * zeroDecayWeight (1 / 2) z := by sorry
