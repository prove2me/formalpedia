-- Prove2me | Theorems.Thm_ModularCurve_exists_addMonoidHom_exp_eq_of_norm_eq_one_of_trace_sq_le_four_of_finiteIndex
-- name    : ModularCurve.exists_addMonoidHom_exp_eq_of_norm_eq_one_of_trace_sq_le_four_of_finiteIndex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/fbab06d0-5776-5292-be1f-1bae81cf242a
-- title:
--   Unitary characters trivial on tr²≤ 4 have real logarithms
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$ of finite index, and let $\chi:\Gamma\to\mathbb{C}$ be a function which is multiplicative, $\chi(\gamma\delta)=\chi(\gamma)\chi(\delta)$ for all $\gamma,\delta\in\Gamma$, which takes values of absolute value $1$, $\|\chi(\gamma)\|=1$ for all $\gamma$, and which satisfies $\chi(\gamma)=1$ for every $\gamma\in\Gamma$ whose image in $\mathrm{Matrix}(\mathrm{Fin}\,2)(\mathrm{Fin}\,2)\,\mathbb{Z}$ has trace $t$ with $t^2\le 4$ (that is, $t\in\{0,\pm1,\pm2\}$: the elliptic and parabolic elements together with $\pm I$). The assertion is that there exists a homomorphism $\varphi$ from $\Gamma$, written additively via `Additive`, to the additive group $\mathbb{R}$, such that $\varphi(\gamma)=0$ for every $\gamma\in\Gamma$ whose trace $t$ satisfies $t^2\le 4$, and such that $\chi(\gamma)=\exp\bigl(2\pi i\,\varphi(\gamma)\bigr)$ for all $\gamma\in\Gamma$, the real number $\varphi(\gamma)$ being regarded as a complex number.
--
--   This is the multiplicative form of the torsion-freeness of the quotient of $\Gamma^{\mathrm{ab}}$ by the classes of the elements with $\mathrm{tr}^2\le 4$, i.e. of $H_1$ of the compactified modular curve attached to $\Gamma$: a unitary character trivial on those elements admits a real additive logarithm vanishing on them. It is stated for an arbitrary finite-index subgroup, with no congruence assumption and without requiring $-I\in\Gamma$, and it is used in the construction of the real period of a multiplier system for cusp forms via [`ModularCurve.exists_cuspForm_multiplier_eq_exp_periodOf_of_norm_eq_one`](thm.html#ModularCurve.exists_cuspForm_multiplier_eq_exp_periodOf_of_norm_eq_one); the proof invokes the lifting of parabolic homomorphisms with values in $\mathbb{Z}/n\mathbb{Z}$ that kill the finite-order elements to homomorphisms with values in $\mathbb{Z}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_addMonoidHom_exp_eq_of_norm_eq_one_of_trace_sq_le_four_of_finiteIndex.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_addMonoidHom_exp_eq_of_norm_eq_one_of_trace_sq_le_four_of_finiteIndex
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (χ : Γ → ℂ)
    (hmul : ∀ γ δ, χ (γ * δ) = χ γ * χ δ) (hunit : ∀ γ, ‖χ γ‖ = 1)
    (htriv : ∀ γ : Γ,
      ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 → χ γ = 1) :
    ∃ φ : Additive Γ →+ ℝ,
      (∀ γ : Γ,
        ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 → φ (Additive.ofMul γ) = 0) ∧
      ∀ γ, χ γ = Complex.exp (2 * Real.pi * Complex.I * (φ (Additive.ofMul γ) : ℂ)) := by sorry
