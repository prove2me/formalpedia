-- Prove2me | Theorems.Thm_ModularCurve_StarBank_eisInt_series
-- name    : ModularCurve.StarBank.eisInt_series
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/c94d7baa-e8cf-5c0b-a2c8-ce38cfa7f6ea
-- title:
--   Integral model of num(B_{ℓ-1})E_{ℓ-1}, positive coefficients divisible by ℓ
-- statement:
--   Let $\ell$ be a prime with $5 \le \ell$, and let $hk$ be a proof of $3 \le \ell - 1$ (natural subtraction), which serves as the index needed to form Mathlib's normalised level-one Eisenstein series `ModularForm.E hk` of weight $\ell - 1$. Write $B_{\ell-1}$ for the $(\ell-1)$-st Bernoulli number, a rational number, and $\mathrm{num}(B_{\ell-1})$ for its numerator in lowest terms. The assertion is the existence of a formal power series $T$ with integer coefficients such that: the image of $T$ under the coefficientwise ring homomorphism $\mathbb{Z} \to \mathbb{C}$ equals $\mathrm{num}(B_{\ell-1})$ times the $q$-expansion of width $1$ of the underlying function of `ModularForm.E hk` on the upper half-plane; the constant coefficient of $T$ is $\mathrm{num}(B_{\ell-1})$; and for every $m \ge 1$ the coefficient of $q^m$ in $T$ is divisible by $\ell$ in $\mathbb{Z}$. Note that $hk$ follows from $5 \le \ell$ but is required to name the Eisenstein series.
--
--   This is the integral form of the congruence $E_{\ell-1} \equiv 1 \pmod \ell$ for the normalised weight $\ell-1$ level-one Eisenstein series, in the shape of an explicit integral power series whose reduction modulo $\ell$ is constant up to the unit $\mathrm{num}(B_{\ell-1})$. It feeds the construction of integral $q$-expansion data for level-one and level-$N$ modular forms, and is used in the constructions built around [`ModularCurve.StarBank.starBank`](thm.html#ModularCurve.StarBank.starBank) and in the integrality statements for the Igusa function field of $X_1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_StarBank_eisInt_series.lean

import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped ArithmeticFunction.sigma
open Finset

theorem ModularCurve.StarBank.eisInt_series {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (hk : 3 ≤ ℓ - 1) :
    ∃ T : PowerSeries ℤ,
      T.map (Int.castRingHom ℂ)
        = ((bernoulli (ℓ - 1)).num : ℂ) • UpperHalfPlane.qExpansion 1 (⇑(ModularForm.E hk))
      ∧ PowerSeries.constantCoeff T = (bernoulli (ℓ - 1)).num
      ∧ ∀ m, 1 ≤ m → (ℓ : ℤ) ∣ T.coeff m := by sorry
