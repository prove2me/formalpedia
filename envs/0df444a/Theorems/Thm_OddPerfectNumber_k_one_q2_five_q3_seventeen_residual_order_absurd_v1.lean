-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_residual_order_absurd_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_residual_order_absurd_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T16:51:35.561979+00:00
-- url     : https://prove2.me/theorems/00813c46-68c1-487b-ac3e-45ef82c16760
-- title:
--   Finite q3=17 residual order-index contradiction
-- statement:
--   Once the q3=17 finite reduction supplies one of the four residual D/q4 lists and the prime-index geometric-sum lemma supplies primality of orderOf 3 modulo q4, every listed order is either even, composite, or q4=511 is nonprime. This terminal child is deliberately independent of the upstream reduction.
-- source:
--   Finite arithmetic terminal for the researched q3=17 residual candidates; it records no canonical reduction or source-generation claim.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_residual_order_absurd_v1 (D q4 : Nat) (hq4 : q4.Prime) (hcase : (D = 135 ∧ ((q4 = 1021 ∧ orderOf (3 : ZMod q4) = 34) ∨ (q4 = 1531 ∧ orderOf (3 : ZMod q4) = 170) ∨ (q4 = 2551 ∧ orderOf (3 : ZMod q4) = 150) ∨ (q4 = 3061 ∧ orderOf (3 : ZMod q4) = 1530) ∨ (q4 = 3571 ∧ orderOf (3 : ZMod q4) = 3570) ∨ (q4 = 4591 ∧ orderOf (3 : ZMod q4) = 270))) ∨ (D = 225 ∧ ((q4 = 103 ∧ orderOf (3 : ZMod q4) = 34) ∨ (q4 = 137 ∧ orderOf (3 : ZMod q4) = 136) ∨ (q4 = 239 ∧ orderOf (3 : ZMod q4) = 119) ∨ (q4 = 307 ∧ orderOf (3 : ZMod q4) = 34) ∨ (q4 = 409 ∧ orderOf (3 : ZMod q4) = 204) ∨ (q4 = 443 ∧ orderOf (3 : ZMod q4) = 221))) ∨ (D = 255 ∧ q4 = 511) ∨ (D = 289 ∧ ((q4 = 31 ∧ orderOf (3 : ZMod q4) = 30) ∨ (q4 = 61 ∧ orderOf (3 : ZMod q4) = 10) ∨ (q4 = 151 ∧ orderOf (3 : ZMod q4) = 50) ∨ (q4 = 181 ∧ orderOf (3 : ZMod q4) = 45) ∨ (q4 = 211 ∧ orderOf (3 : ZMod q4) = 210) ∨ (q4 = 241 ∧ orderOf (3 : ZMod q4) = 120) ∨ (q4 = 271 ∧ orderOf (3 : ZMod q4) = 30) ∨ (q4 = 331 ∧ orderOf (3 : ZMod q4) = 330) ∨ (q4 = 421 ∧ orderOf (3 : ZMod q4) = 105)))) (hindex : Nat.Prime (orderOf (3 : ZMod q4))) : False := by
  sorry

end OddPerfectNumber
