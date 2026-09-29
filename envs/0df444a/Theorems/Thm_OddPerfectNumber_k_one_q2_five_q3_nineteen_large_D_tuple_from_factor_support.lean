-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_tuple_from_factor_support
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_tuple_from_factor_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T15:22:26.193232+00:00
-- url     : https://prove2.me/theorems/4068168b-4bea-4823-85ab-2ec38f5e1b51
-- title:
--   q3=19 large-D tuple arithmetic from finite factor support
-- statement:
--   Given the six q4 cases, the finite abundance windows, and the explicit four-prime factor-support form of D, exact arithmetic leaves only D=855, q4=101, p=1709.
-- source:
--   Finite exponent enumeration under the supplied factor-support form and six exact abundance windows; no source/order argument is used.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_large_D_tuple_from_factor_support (D p q4 i j k l : Nat) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4cases : q4 = 97 ∨ q4 = 101 ∨ q4 = 103 ∨ q4 = 107 ∨ q4 = 109 ∨ q4 = 113) (hform : D = 3^i * 5^j * 19^k * q4^l) (hi : i ≤ 7) (hj : j ≤ 5) (hk : k ≤ 2) (hl : l ≤ 1) (hwindow : (q4 = 97 ∧ 2881 ≤ D ∧ D ≤ 4608) ∨ (q4 = 101 ∧ 854 ≤ D ∧ D ≤ 960) ∨ (q4 = 103 ∧ 642 ≤ D ∧ D ≤ 699) ∨ (q4 = 107 ∧ 437 ≤ D ∧ D ≤ 462) ∨ (q4 = 109 ∧ 379 ≤ D ∧ D ≤ 398) ∨ (q4 = 113 ∧ 304 ≤ D ∧ D ≤ 316)) : D = 855 ∧ q4 = 101 ∧ p = 1709 := by sorry

end OddPerfectNumber
