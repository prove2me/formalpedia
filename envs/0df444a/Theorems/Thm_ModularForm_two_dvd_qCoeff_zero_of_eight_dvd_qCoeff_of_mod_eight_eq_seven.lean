-- Prove2me | Theorems.Thm_ModularForm_two_dvd_qCoeff_zero_of_eight_dvd_qCoeff_of_mod_eight_eq_seven
-- name    : ModularForm.two_dvd_qCoeff_zero_of_eight_dvd_qCoeff_of_mod_eight_eq_seven
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/d4e7733a-c5a9-5235-ae51-748ff4e7e786
-- title:
--   Parity of the constant term when p ≡ 7 (mod 8)
-- statement:
--   Let $p$ be a prime with $p \equiv 7 \pmod 8$, let $h$ be a holomorphic modular form of weight $2$ for the congruence subgroup $\Gamma_0(p)$, and let $b : \mathbb{N} \to \mathbb{Z}$ be a sequence of rational integers which represents the $q$-expansion of $h$ at the cusp $\infty$ in the sense that for every $n$ the complex number $b_n$ equals [`ModularFormClass.qCoeff h n`](def/FLTPrelim_Modularity.html#L19), the $n$-th coefficient of the $q$-expansion of $h$ taken with width $1$, i.e. the coefficient of $q^n$ in $h = \sum_{n \ge 0} b_n q^n$ with $q = e^{2\pi i z}$. Assume that $8 \mid b_n$ for every $n \ne 0$. Then $2 \mid b_0$. In words: a weight-two form on $\Gamma_0(p)$ with integral $q$-expansion cannot be congruent modulo $8$ to an odd constant. The congruence $p \equiv 7 \pmod 8$ enters the proof only through the resulting coprimality of $8$ and $p$, so the conclusion as formalised in fact holds for every odd prime $p$.
--
--   This is the $2$-primary case $M = 8$ of Mazur's constant-term theorem for weight-two forms on $\Gamma_0(p)$, in the residue class $p \equiv -1 \pmod 8$; it is the instance of that theorem which elementary trace-to-level-one arguments do not reach, since they only give $8 \mid (p+1)b_0$. It is used by [`ModularForm.two_dvd_qCoeff_zero_of_eight_dvd_qCoeff`](thm.html#ModularForm.two_dvd_qCoeff_zero_of_eight_dvd_qCoeff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_two_dvd_qCoeff_zero_of_eight_dvd_qCoeff_of_mod_eight_eq_seven.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.two_dvd_qCoeff_zero_of_eight_dvd_qCoeff_of_mod_eight_eq_seven (p : ℕ)
    [Fact p.Prime] (hp : p % 8 = 7) (h : ModularForm (CongruenceSubgroup.Gamma0 p) 2) (b : ℕ → ℤ)
    (hb : ∀ n : ℕ, (b n : ℂ) = ModularFormClass.qCoeff h n)
    (hdvd : ∀ n : ℕ, n ≠ 0 → (8 : ℤ) ∣ b n) : (2 : ℤ) ∣ b 0 := by sorry
