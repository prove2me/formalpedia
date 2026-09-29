-- Prove2me | Theorems.Thm_ModularForm_exists_levelOne_esymm_qExpansion_congr_of_gamma0_two
-- name    : ModularForm.exists_levelOne_esymm_qExpansion_congr_of_gamma0_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/13da6fa4-0c62-5ab6-b228-37531eec9199
-- title:
--   Level-one forms from symmetric functions of Γ₀(p)-translates
-- statement:
--   Let $p$ be a prime, let $h$ be a modular form of weight $2$ for $\Gamma_0(p)$, and let $B \in \mathbb{Z}[[q]]$ be an integral power series whose image under the coefficientwise map $\mathbb{Z} \to \mathbb{C}$ is the $q$-expansion of $h$ at $\infty$ taken with period $1$; thus $B$ is an integral model of the expansion $h = \sum_{n \ge 0} b_n q^n$. Let $M$ be an integer dividing the $n$-th coefficient of $B$ for every $n \ge 1$, and let $r$ be a natural number with $r \ge 1$. The conclusion asserts the existence of a modular form $F$ of weight $2r$ for the full modular group $\mathrm{SL}_2(\mathbb{Z})$ (written $\mathcal{SL}$, viewed inside $\mathrm{GL}_2(\mathbb{R})$) together with a power series $T \in \mathbb{Z}[[q]]$ such that: the image of $T$ in $\mathbb{C}[[q]]$ is the $q$-expansion of $F$ at $\infty$ with period $1$; $M$ divides the $n$-th coefficient of $T$ for every $n \ge 1$; and $M$ divides $$\mathrm{constantCoeff}\,T - (-\,\mathrm{constantCoeff}\,B)^r\Bigl(\binom{p}{r} - p\binom{p}{r-1}\Bigr),$$ i.e. the constant term of $T$ is congruent to $(-b_0)^r(\binom{p}{r} - p\binom{p}{r-1})$ modulo $M$.
--
--   This is the construction, going back to Serre and used by Mazur in his study of the Eisenstein ideal, of level-one forms out of the elementary symmetric functions of the $p+1$ translates of a weight-two form on $\Gamma_0(p)$ by coset representatives of $\Gamma_0(p)$ in $\mathrm{SL}_2(\mathbb{Z})$, the congruence for the constant term coming from the identification of the Fricke transform of $h$ with $-U_p h$. It is used by [`ModularForm.dvd_qCoeff_zero_of_prime_ne_level_dvd_qCoeff`](thm.html#ModularForm.dvd_qCoeff_zero_of_prime_ne_level_dvd_qCoeff), where the absence of level-one forms of low weight forces divisibility of the constant term as well; the proof invokes the vanishing of $U_p h + h\mid_2 W_p$, the formula for the $q$-coefficients of $U_p$, and the passage from forms on $\Gamma_0(p)$ to forms on $\mathrm{SL}_2(\mathbb{Z})$ via $p^{k-2}X + U_p(X\mid_k W_p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_levelOne_esymm_qExpansion_congr_of_gamma0_two.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem ModularForm.exists_levelOne_esymm_qExpansion_congr_of_gamma0_two (p : ℕ) [Fact p.Prime]
    (h : ModularForm (CongruenceSubgroup.Gamma0 p) 2) {B : PowerSeries ℤ}
    (hB : B.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 ⇑h) (M : ℤ)
    (hdvd : ∀ n : ℕ, 1 ≤ n → M ∣ B.coeff n) {r : ℕ} (hr : 1 ≤ r) :
    ∃ (F : ModularForm 𝒮ℒ (2 * r)) (T : PowerSeries ℤ),
      T.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 ⇑F ∧
      (∀ n : ℕ, 1 ≤ n → M ∣ T.coeff n) ∧
      M ∣ PowerSeries.constantCoeff T -
        (-PowerSeries.constantCoeff B) ^ r * ((p.choose r : ℤ) - p * (p.choose (r - 1) : ℤ)) := by sorry
