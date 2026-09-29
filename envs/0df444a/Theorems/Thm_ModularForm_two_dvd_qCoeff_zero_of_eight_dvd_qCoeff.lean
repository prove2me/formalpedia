-- Prove2me | Theorems.Thm_ModularForm_two_dvd_qCoeff_zero_of_eight_dvd_qCoeff
-- name    : ModularForm.two_dvd_qCoeff_zero_of_eight_dvd_qCoeff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/2b9c6a28-269a-545d-bc64-cf2cdc4ded50
-- title:
--   2 ∣ b₀ for weight-two forms on Γ₀(p) with 8 ∣ bₙ
-- statement:
--   Let $p$ be a prime with $p \neq 2$, and let $h$ be a modular form of weight $2$ for the congruence subgroup $\Gamma_0(p)$. Let $b : \mathbb{N} \to \mathbb{Z}$ be a sequence of integers which represents the $q$-expansion coefficients of $h$ at the cusp $\infty$, in the sense that for every $n$ the complex number $(b_n : \mathbb{C})$ equals [`ModularFormClass.qCoeff h n`](def/FLTPrelim_Modularity.html#L19), the $n$-th coefficient of the $q$-expansion of $h$ of width $1$ (that is, of `qExpansion 1 h`). Assume that $8 \mid b_n$ for every $n \neq 0$. The conclusion is that $2 \mid b_0$. Thus a weight-two form on $\Gamma_0(p)$, $p$ odd, with integral $q$-expansion congruent to the constant $b_0$ modulo $8$ has $b_0$ even; the hypothesis forces only divisibility by $2$, not by $4$ or $8$, of the constant term.
--
--   This is the $2$-primary case, with modulus $M = 8$, of Mazur's divisibility statement that $M \mid b_n$ for all $n \ge 1$ and $\gcd(M,p)=1$ imply $M \mid 12\,b_0$ for a weight-two form on $\Gamma_0(p)$. It feeds into [`ModularForm.dvd_twelve_mul_qCoeff_zero_of_forall_dvd_qCoeff`](thm.html#ModularForm.dvd_twelve_mul_qCoeff_zero_of_forall_dvd_qCoeff), the form of that divisibility used later in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_two_dvd_qCoeff_zero_of_eight_dvd_qCoeff.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.two_dvd_qCoeff_zero_of_eight_dvd_qCoeff (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (h : ModularForm (CongruenceSubgroup.Gamma0 p) 2) (b : ℕ → ℤ)
    (hb : ∀ n : ℕ, (b n : ℂ) = ModularFormClass.qCoeff h n)
    (hdvd : ∀ n : ℕ, n ≠ 0 → (8 : ℤ) ∣ b n) : (2 : ℤ) ∣ b 0 := by sorry
