-- Prove2me | Theorems.Thm_ModularForm_sub_one_dvd_weight_of_qExpansion_congr_const_levelOne
-- name    : ModularForm.sub_one_dvd_weight_of_qExpansion_congr_const_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/c44634ec-d5fb-5f1a-a9ff-2f4ebbb99bd5
-- title:
--   Swinnerton-Dyer weight congruence: (ℓ-1) ∣ k
-- statement:
--   Let $\ell$ be a prime with $\ell \ge 5$, let $k$ be an integer, and let $f$ be a modular form of weight $k$ for the full modular group $\mathrm{SL}_2(\mathbb{Z})$. Suppose given a power series $T$ with coefficients in $\mathbb{Z}$ whose image under coefficientwise application of $\mathbb{Z} \to \mathbb{C}$ is the $q$-expansion of $f$ at level $1$ (so $T$ witnesses that the Fourier coefficients of $f$ at the cusp are rational integers). Assume that $\ell$ divides the $n$-th coefficient of $T$ for every $n \ge 1$, and that $\ell$ does not divide the constant coefficient of $T$; equivalently, the reduction of $T$ modulo $\ell$ is a non-zero constant. The conclusion is that $\ell - 1$, formed as a natural number and then regarded as an integer, divides $k$ in $\mathbb{Z}$. Note that $k$ is an arbitrary integer here, no positivity or parity being assumed.
--
--   This is the weight congruence of Swinnerton-Dyer and Serre: the graded algebra of level-one modular forms modulo $\ell$ is $\mathbb{F}_\ell[Q,R]/(\tilde{E}_{\ell-1}-1)$, graded by weight modulo $\ell-1$, so a form whose reduction is a non-zero constant must have weight divisible by $\ell-1$. It is used in the proof of [`ModularForm.dvd_qCoeff_zero_of_prime_ne_level_dvd_qCoeff`](thm.html#ModularForm.dvd_qCoeff_zero_of_prime_ne_level_dvd_qCoeff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_sub_one_dvd_weight_of_qExpansion_congr_const_levelOne.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem ModularForm.sub_one_dvd_weight_of_qExpansion_congr_const_levelOne {ℓ : ℕ}
    (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) {k : ℤ} (f : ModularForm 𝒮ℒ k) {T : PowerSeries ℤ}
    (hT : T.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 ⇑f)
    (hdvd : ∀ n : ℕ, 1 ≤ n → (ℓ : ℤ) ∣ T.coeff n)
    (h0 : ¬ (ℓ : ℤ) ∣ PowerSeries.constantCoeff T) :
    ((ℓ - 1 : ℕ) : ℤ) ∣ k := by sorry
