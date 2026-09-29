-- Prove2me | Theorems.Thm_ModularForm_exists_modularForm_mul_eq_of_analyticOrderAt_le
-- name    : ModularForm.exists_modularForm_mul_eq_of_analyticOrderAt_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/89983266-b75b-5ca9-893c-22347e795f2e
-- title:
--   Division of modular forms on Γ₀(N)
-- statement:
--   Let $N$ be a natural number, let $a,b,c$ be integers with $b+c=a$, and let $\Phi$ be a modular form of weight $a$ and $\Psi$ a modular form of weight $b$ for the congruence subgroup $\Gamma_0(N)$, with $\Psi\neq 0$. Assume two conditions. First, at every point $\tau$ of the upper half-plane the analytic order of vanishing of $\Psi$ is at most that of $\Phi$; here both forms are read as functions of a complex variable by composing with the partial section $\mathbb{C}\to\mathfrak{H}$, and the orders are compared as elements of $\mathbb{N}\cup\{\infty\}$ at the point $\tau$ viewed in $\mathbb{C}$. Second, for every $A\in\mathrm{SL}_2(\mathbb{Z})$ there is a real constant $C$ such that, eventually along the filter of points of $\mathfrak{H}$ with imaginary part tending to infinity, $\|(\Phi\mid_a A)(\tau)\|\le C\,\|(\Psi\mid_b A)(\tau)\|$, the weight-$a$ and weight-$b$ slash actions being those of the image of $A$ in $\mathrm{GL}_2(\mathbb{R})$. The conclusion is that there exists a modular form $f$ of weight $c$ for $\Gamma_0(N)$ with $f(\tau)\,\Psi(\tau)=\Phi(\tau)$ for every $\tau$ in the upper half-plane.
--
--   This is the division statement for the graded ring of modular forms on $\Gamma_0(N)$: a pointwise inequality of vanishing orders on $\mathfrak{H}$ together with a growth bound $\Phi\mid A = O(\Psi\mid A)$ at each cusp forces the quotient $\Phi/\Psi$ to be a modular form of the complementary weight. It is used to extract a modular form from a quotient in [`ModularCurve.exists_modularForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral`](thm.html#ModularCurve.exists_modularForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral), and is the $O(\cdot)$ counterpart of the version whose cusp hypothesis produces a cusp form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_modularForm_mul_eq_of_analyticOrderAt_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups ModularForm

theorem ModularForm.exists_modularForm_mul_eq_of_analyticOrderAt_le (N : ℕ) {a b : ℤ} (c : ℤ) (habc : b + c = a)
    (Φ : ModularForm (CongruenceSubgroup.Gamma0 N) a) (Ψ : ModularForm (CongruenceSubgroup.Gamma0 N) b) (hΨ : Ψ ≠ 0)
    (hord : ∀ τ : UpperHalfPlane, analyticOrderAt ((Ψ : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) (τ : ℂ) ≤
      analyticOrderAt ((Φ : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) (τ : ℂ))
    (hcusp : ∀ A : Matrix.SpecialLinearGroup (Fin 2) ℤ, ∃ C : ℝ,
      ∀ᶠ τ : UpperHalfPlane in UpperHalfPlane.atImInfty,
        ‖((Φ : UpperHalfPlane → ℂ) ∣[a] (A : GL (Fin 2) ℝ)) τ‖ ≤ C * ‖((Ψ : UpperHalfPlane → ℂ) ∣[b] (A : GL (Fin 2) ℝ)) τ‖) :
    ∃ f : ModularForm (CongruenceSubgroup.Gamma0 N) c, ∀ τ : UpperHalfPlane, f τ * Ψ τ = Φ τ := by sorry
