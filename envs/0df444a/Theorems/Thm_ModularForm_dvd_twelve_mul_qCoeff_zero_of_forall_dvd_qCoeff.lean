-- Prove2me | Theorems.Thm_ModularForm_dvd_twelve_mul_qCoeff_zero_of_forall_dvd_qCoeff
-- name    : ModularForm.dvd_twelve_mul_qCoeff_zero_of_forall_dvd_qCoeff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/f98ac73d-38df-5123-86ae-d12f1d122f09
-- title:
--   M ∣ 12b₀ for constant reductions on Γ₀(p)
-- statement:
--   Let $p$ and $M$ be natural numbers with $p$ prime and $\gcd(p,M)=1$, and let $h$ be a holomorphic modular form of weight $2$ for the congruence subgroup $\Gamma_0(p)$. Let $b : \mathbb{N} \to \mathbb{Z}$ be an integer sequence which computes the $q$-expansion coefficients of $h$ at the cusp $\infty$ taken with width $1$: for every $n$, the complex number $b_n$ equals the $n$-th coefficient of `qExpansion 1` of (the function underlying) $h$, so that $h$ has integral coefficients with $h = \sum_{n\ge 0} b_n q^n$. Assume that $M$ divides $b_n$ in $\mathbb{Z}$ for every $n \neq 0$, i.e. that the reduction of the $q$-expansion modulo $M$ is the constant $b_0$. The conclusion is the divisibility $M \mid 12\,b_0$ in $\mathbb{Z}$. No positivity assumption on $M$ is imposed beyond $M$ being a natural number coprime to $p$ (for $M = 0$ the hypothesis and conclusion read as equalities of coefficients with $0$).
--
--   This is the integral constant-term bound for weight-two forms on $\Gamma_0(p)$ in the shape used by Mazur: a weight-two form on $\Gamma_0(p)$ whose $q$-expansion is constant modulo $M$, with $p \nmid M$, has $12$ times that constant killed by $M$. It is used in the project to compare $q$-expansion coefficients with divisor-sum functions, through [`CuspForm.dvd_half_sub_one_of_qCoeff_congr_sigmaPrimeTo`](thm.html#CuspForm.dvd_half_sub_one_of_qCoeff_congr_sigmaPrimeTo).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_dvd_twelve_mul_qCoeff_zero_of_forall_dvd_qCoeff.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.dvd_twelve_mul_qCoeff_zero_of_forall_dvd_qCoeff (p M : ℕ) [Fact p.Prime]
    (hpM : Nat.Coprime p M) (h : ModularForm (CongruenceSubgroup.Gamma0 p) 2) (b : ℕ → ℤ)
    (hb : ∀ n : ℕ, (b n : ℂ) = ModularFormClass.qCoeff h n)
    (hdvd : ∀ n : ℕ, n ≠ 0 → (M : ℤ) ∣ b n) : (M : ℤ) ∣ 12 * b 0 := by sorry
