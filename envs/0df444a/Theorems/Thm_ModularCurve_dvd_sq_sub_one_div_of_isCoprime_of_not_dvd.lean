-- Prove2me | Theorems.Thm_ModularCurve_dvd_sq_sub_one_div_of_isCoprime_of_not_dvd
-- name    : ModularCurve.dvd_sq_sub_one_div_of_isCoprime_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/755a2d01-c471-5d60-93b7-8a44499d7989
-- title:
--   Elementary divisibility: m ∣ (p²-1)/24
-- statement:
--   Let $p$ and $m$ be natural numbers with $p$ prime, and let $a_1$ and $\tau$ be integers. Assume that $a_1$ and the image of $m$ in $\mathbb{Z}$ are coprime in the Bézout sense (some integral combination $u a_1 + v m$ equals $1$), that $p \nmid m$, and that the integer $24m$ divides both $a_1(p-1)\tau$ and $a_1(p-1)\bigl(\tau^2 - p^{11}(p+1)\bigr)$. The conclusion is that $m$ divides $(p^2-1)/24$, the quotient being truncated division of natural numbers; in particular for $p = 2$ and $p = 3$ the quotient is $0$ and the conclusion is vacuous, while for $p \ge 5$ it is equivalent to the divisibility $24m \mid p^2-1$. The exponent $11$ and the factor $24$ are exactly as written; no positivity or nonvanishing hypothesis on $m$, $a_1$ or $\tau$ is imposed beyond those listed.
--
--   This is the elementary arithmetic assembly step behind bounds of the shape $m \mid (p^2-1)/24$ arising from Eisenstein-type congruences, in the formulation of Mazur's Modular curves and the Eisenstein ideal, II.5.12(iii). It is used by [`CuspForm.dvd_sq_sub_one_div_of_qCoeff_congr_sigmaPrimeTo`](thm.html#CuspForm.dvd_sq_sub_one_div_of_qCoeff_congr_sigmaPrimeTo), where $a_1$ and $\tau$ come from $q$-expansion coefficients and the two divisibilities express congruences modulo $24m$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_dvd_sq_sub_one_div_of_isCoprime_of_not_dvd.lean

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.Coprime.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.dvd_sq_sub_one_div_of_isCoprime_of_not_dvd (p m : ℕ) (hp : p.Prime) (a1 tau : ℤ) (h1 : IsCoprime a1 (m : ℤ)) (hpm : ¬ p ∣ m) (hC1 : (24 * m : ℤ) ∣ a1 * ((p : ℤ) - 1) * tau) (hC2 : (24 * m : ℤ) ∣ a1 * ((p : ℤ) - 1) * (tau ^ 2 - (p : ℤ) ^ 11 * ((p : ℤ) + 1))) : m ∣ (p ^ 2 - 1) / 24 := by sorry
