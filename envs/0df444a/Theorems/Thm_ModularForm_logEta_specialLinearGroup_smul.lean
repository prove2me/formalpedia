-- Prove2me | Theorems.Thm_ModularForm_logEta_specialLinearGroup_smul
-- name    : ModularForm.logEta_specialLinearGroup_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/83c6d476-80dd-5212-96d4-a24c202a790f
-- title:
--   Dedekind's η transformation law in logarithmic form
-- statement:
--   Let $\gamma$ be an element of $\mathrm{SL}_2(\mathbb Z)$, written with integer entries $a = \gamma_{00}$, $b = \gamma_{01}$, $c = \gamma_{10}$, $d = \gamma_{11}$, and assume $c > 0$; let $z$ lie in the upper half-plane. Consider the expression $L(w) = \pi i w/12 + \sum_{n=0}^{\infty} \log\bigl(1 - \mathtt{eta\_q}\,n\,w\bigr)$, where $\mathtt{eta\_q}\,n\,w = e^{2\pi i (n+1) w}$ and $\log$ is the principal branch applied termwise, the sum being a `tsum` over $n \in \mathbb N$. The assertion is the identity $$L(\gamma\cdot z) = L(z) + \tfrac12\log\bigl(-i\,(cz+d)\bigr) + \frac{\pi i}{12}\,\Bigl(\frac{a+d}{c} - 12\,s(d,c)\Bigr),$$ in which $\gamma\cdot z$ is the Möbius action on the upper half-plane, $c$ is taken as the natural number `Int.toNat c` in the last bracket, the bracket is formed in $\mathbb Q$ and then cast to $\mathbb C$, and $s(d,c) = \mathtt{dedekindSum}\ d\ c$ is defined as $\sum_{r=0}^{c-1} \big(\!\big(r/c\big)\!\big)\,\big(\!\big(dr/c\big)\!\big)$ with $\big(\!\big(x\big)\!\big) = \mathtt{dedekindSaw}\,x$ equal to $0$ when the fractional part of $x$ vanishes and to $\{x\} - 1/2$ otherwise.
--
--   This is Dedekind's transformation law for $\eta$ in its logarithmic (additive) form, with the Rademacher function $\Phi(\gamma) = (a+d)/c - 12\,s(d,c)$ appearing explicitly; the multiplicative law for $\eta$ itself is its exponential. It is used in the study of the $\eta$-quotient units and cuspidal divisor classes on modular curves, being cited by [`ModularCurve.eisensteinNumerator_dvd_mul_of_witness`](thm.html#ModularCurve.eisensteinNumerator_dvd_mul_of_witness), [`ModularCurve.exists_continuous_pow_eq_of_isPrincipal_smul_cuspidalDivisor`](thm.html#ModularCurve.exists_continuous_pow_eq_of_isPrincipal_smul_cuspidalDivisor) and [`ModularCurve.sharpUnitNecessary_of_witness`](thm.html#ModularCurve.sharpUnitNecessary_of_witness).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_logEta_specialLinearGroup_smul.lean

import Definitions.Def_NumberTheory_DedekindSum
import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.logEta_specialLinearGroup_smul (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hc : 0 < (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) (z : UpperHalfPlane) : (Real.pi * Complex.I * ((γ • z : UpperHalfPlane) : ℂ) / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n ((γ • z : UpperHalfPlane) : ℂ))) = (Real.pi * Complex.I * (z : ℂ) / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n (z : ℂ))) + Complex.log (-Complex.I * (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (z : ℂ) + ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ))) / 2 + Real.pi * Complex.I / 12 * (((((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℚ) / ((((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0).toNat : ℕ) : ℚ) - 12 * dedekindSum ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0).toNat : ℚ) : ℂ) := by sorry
