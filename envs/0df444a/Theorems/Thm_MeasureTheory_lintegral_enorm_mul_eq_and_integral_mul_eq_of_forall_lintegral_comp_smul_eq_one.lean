-- Prove2me | Theorems.Thm_MeasureTheory_lintegral_enorm_mul_eq_and_integral_mul_eq_of_forall_lintegral_comp_smul_eq_one
-- name    : MeasureTheory.lintegral_enorm_mul_eq_and_integral_mul_eq_of_forall_lintegral_comp_smul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/daf86f95-d066-5c6c-b78f-d99a580b6e69
-- title:
--   Independence of orbit integrals from the section function
-- statement:
--   Let $A$ be a group with a measurable space structure for which inversion is measurable, acting on a measurable space $X$ in such a way that the map $A \times X \to X$, $(a,x) \mapsto a \cdot x$, is measurable. Let $\tau$ be an s-finite measure on $A$ invariant under $a \mapsto a^{-1}$, and let $\rho$ be an s-finite measure on $X$ such that for every $a \in A$ the map $x \mapsto a \cdot x$ is measure-preserving from $\rho$ to $\rho$. Let $h \colon X \to \mathbb{C}$ be measurable and $A$-invariant, i.e. $h(a \cdot x) = h(x)$ for all $a \in A$, $x \in X$, and let $w_1, w_2 \colon X \to \mathbb{R}$ be measurable and pointwise nonnegative, each satisfying the section condition $\int_A^{-} \mathrm{ofReal}(w_i(a \cdot x)) \, d\tau(a) = 1$ in $[0,\infty]$ for every $x$ with $h(x) \neq 0$. The conclusion is a conjunction: first, the lower Lebesgue integrals satisfy $\int^{-}_X \|h(x)\|_e \cdot \mathrm{ofReal}(w_1(x)) \, d\rho = \int^{-}_X \|h(x)\|_e \cdot \mathrm{ofReal}(w_2(x)) \, d\rho$ in $[0,\infty]$; second, if $x \mapsto h(x) w_1(x)$ is Bochner integrable for $\rho$, then so is $x \mapsto h(x) w_2(x)$, and the two Bochner integrals over $X$ agree.
--
--   A nonnegative weight $w$ with $\int_A w(a \cdot x) \, d\tau(a) = 1$ on the set where $h$ is nonzero acts as a section function for the action of $A$ on $X$, so that $\int_X h \, w \, d\rho$ represents the integral of the $A$-invariant function $h$ over the orbit space without introducing a quotient measure; the statement asserts that this quantity does not depend on the choice of section function. It is used to replace the section function coming from the definition of a (twisted) orbital integral by a more convenient one, in the estimates for twisted orbital integrals on semi-local integral sets and in the computation of such integrals for the diagonal torus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_lintegral_enorm_mul_eq_and_integral_mul_eq_of_forall_lintegral_comp_smul_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem MeasureTheory.lintegral_enorm_mul_eq_and_integral_mul_eq_of_forall_lintegral_comp_smul_eq_one
    {A X : Type*} [Group A] [MulAction A X] [MeasurableSpace A] [MeasurableInv A] [MeasurableSpace X]
    (hact : Measurable fun z : A × X => z.1 • z.2)
    (τ : Measure A) [SFinite τ] [τ.IsInvInvariant]
    (ρ : Measure X) [SFinite ρ] (hρ : ∀ a : A, MeasurePreserving (fun x : X => a • x) ρ ρ)
    (h : X → ℂ) (hh : Measurable h) (hhA : ∀ (a : A) (x : X), h (a • x) = h x)
    (w₁ w₂ : X → ℝ) (hw₁ : Measurable w₁) (hw₂ : Measurable w₂) (hw₁0 : ∀ x, 0 ≤ w₁ x) (hw₂0 : ∀ x, 0 ≤ w₂ x)
    (hs₁ : ∀ x, h x ≠ 0 → ∫⁻ a, ENNReal.ofReal (w₁ (a • x)) ∂τ = 1)
    (hs₂ : ∀ x, h x ≠ 0 → ∫⁻ a, ENNReal.ofReal (w₂ (a • x)) ∂τ = 1) :
    ∫⁻ x, ‖h x‖ₑ * ENNReal.ofReal (w₁ x) ∂ρ = ∫⁻ x, ‖h x‖ₑ * ENNReal.ofReal (w₂ x) ∂ρ ∧
      (Integrable (fun x => h x * (w₁ x : ℂ)) ρ →
        Integrable (fun x => h x * (w₂ x : ℂ)) ρ ∧
          ∫ x, h x * (w₁ x : ℂ) ∂ρ = ∫ x, h x * (w₂ x : ℂ) ∂ρ) := by sorry
