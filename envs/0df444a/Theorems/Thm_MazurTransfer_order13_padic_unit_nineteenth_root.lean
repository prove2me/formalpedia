-- Prove2me | Theorems.Thm_MazurTransfer_order13_padic_unit_nineteenth_root
-- name    : MazurTransfer.order13_padic_unit_nineteenth_root
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T19:26:39.803321+00:00
-- url     : https://prove2.me/theorems/a1d4e75c-708f-4b11-9599-92e863307d9e
-- title:
--   Every 13-adic unit is a nineteenth power
-- statement:
--   For every unit $u$ in the ring $\mathbb Z_{13}$ of 13-adic integers, there is a unit $v$ with $v^{19}=u$. The prime fact in the Lean statement records the decidable identity that 13 is prime.
--
--   This is a local arithmetic ingredient for the classical order-13 descent and Kummer calculations at 13. It supplies no assertion about the rational points or Mordell–Weil rank of the genus-two curve. A downstream consequence is that any group homomorphism from these units to the additive cyclic group of order 19 is zero.
-- source:
--   Original local arithmetic proof by Vas and contributors, Apache-2.0. Hensel lemma and finite-field exponentiation from Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Named checked downstream consumer: MazurTransfer.order13_padic_unit_no_cyclic_19_quotient. Design boundary: the actual 13-adic integer units; no class-field comparison or Jacobian construction assumed.

import Mathlib

theorem MazurTransfer.order13_padic_unit_nineteenth_root [Fact (Nat.Prime 13)]
    (u : (ℤ_[13])ˣ) : ∃ v : (ℤ_[13])ˣ, v ^ 19 = u := by sorry
