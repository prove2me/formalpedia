-- Prove2me | Theorems.Thm_ModularCurve_not_isIntegral_jInt_of_dvd_discriminant_not_dvd_c4
-- name    : ModularCurve.not_isIntegral_jInt_of_dvd_discriminant_not_dvd_c4
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/2e220ae6-fc11-50d8-a041-392e74de1e06
-- title:
--   Non-integrality of j at a prime of multiplicative reduction
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ (given by the usual five coefficients) whose discriminant $\Delta_W$ is non-zero, and let $\ell$ be a prime natural number such that $\ell$, viewed in $\mathbb{Z}$, divides $\Delta_W$ but does not divide the invariant $c_4$ of $W$. The conclusion is that the element $\mathrm{jInt}\,W$ of the algebraic closure of $\mathbb{Q}$, defined as the quotient of the cube of the image of $c_4$ by the image of $\Delta_W$ under the canonical ring map $\mathbb{Z} \to \overline{\mathbb{Q}}$, is not integral over $\mathbb{Z}$, i.e. satisfies no monic polynomial with integer coefficients. Note that the hypotheses are exactly divisibility conditions on $\Delta_W$ and $c_4$: no minimality of the model and no further reduction-type condition is assumed, and the non-vanishing of $\Delta_W$ enters only to make the quotient defining $\mathrm{jInt}\,W$ a genuine division.
--
--   This is the elementary valuation-theoretic statement that a rational $j$-invariant with $v_\ell(j)<0$ — the situation of potentially multiplicative reduction at $\ell$, where $\ell \mid \Delta$ and $\ell \nmid c_4$ — fails to be an algebraic integer. It is used in the study of the modular polynomial, namely in [`ModularCurve.modularPolynomial_rootMultiplicity_jQuotVelu_eq_one`](thm.html#ModularCurve.modularPolynomial_rootMultiplicity_jQuotVelu_eq_one), to exclude integral $j$-invariants at such primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_not_isIntegral_jInt_of_dvd_discriminant_not_dvd_c4.lean

import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.not_isIntegral_jInt_of_dvd_discriminant_not_dvd_c4
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓΔ : (ℓ : ℤ) ∣ W.Δ) (hℓc₄ : ¬ (ℓ : ℤ) ∣ W.c₄) :
    ¬ _root_.IsIntegral ℤ (ModularCurve.jInt W) := by sorry
