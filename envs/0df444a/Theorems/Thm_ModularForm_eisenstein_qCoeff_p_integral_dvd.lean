-- Prove2me | Theorems.Thm_ModularForm_eisenstein_qCoeff_p_integral_dvd
-- name    : ModularForm.eisenstein_qCoeff_p_integral_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/34834225-a16b-5c47-8a29-56eeb84c044a
-- title:
--   p-integral Eisenstein coefficients divisible by p when (p-1)∣ k
-- statement:
--   Let $p$ be a natural number which is prime (as a typeclass hypothesis), let $k$ be a natural number with $3 \le k$ and $k$ even, and assume $p - 1 \mid k$ (truncated subtraction of naturals). Let $m$ be a natural number with $0 < m$. The assertion is that there exist an integer $x$ and a natural number $s$ such that $p \nmid s$, such that the image of $x$ in $\mathbb{C}$ equals $s$ times the $m$-th coefficient of the $q$-expansion of width $1$ at infinity of Mathlib's normalised level-one Eisenstein series `ModularForm.E hk` of weight $k$, and such that $p \mid x$ in $\mathbb{Z}$. Equivalently: the $m$-th $q$-expansion coefficient of $E_k$ is $x/s$ with $s$ a $p$-unit integer and $p \mid x$, so that coefficient is $p$-integral and lies in $p\mathbb{Z}_p$; since the statement concerns only indices $m \ge 1$, it expresses the congruence $E_k \equiv 1 \pmod p$ coefficientwise, the constant term not being addressed.
--
--   This is the von Staudt–Clausen input to Serre's congruence $E_{p-1} \equiv 1 \pmod p$ for level-one Eisenstein series, in the coefficientwise form needed for weight-raising arguments. It is used in the project's lemmas producing, from a form with $p$-integral $q$-expansion, congruent forms of higher weight or smaller level, including [`CuspForm.exists_weight_ge_qCoeff_congr_level_div_of_alSlash_p_integral`](thm.html#CuspForm.exists_weight_ge_qCoeff_congr_level_div_of_alSlash_p_integral) and [`CuspForm.exists_forall_weight_add_mul_qCoeff_congr_gammaH_level_div_of_alSlash_diamondLinH_p_integral`](thm.html#CuspForm.exists_forall_weight_add_mul_qCoeff_congr_gammaH_level_div_of_alSlash_diamondLinH_p_integral).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_eisenstein_qCoeff_p_integral_dvd.lean

import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularForm.eisenstein_qCoeff_p_integral_dvd (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k)
    (hpk : p - 1 ∣ k) (m : ℕ) (hm : 0 < m) :
    ∃ (x : ℤ) (s : ℕ), ¬ p ∣ s ∧
      (x : ℂ) = s * (PowerSeries.coeff m) (UpperHalfPlane.qExpansion 1 ⇑(ModularForm.E hk)) ∧
      (p : ℤ) ∣ x := by sorry
