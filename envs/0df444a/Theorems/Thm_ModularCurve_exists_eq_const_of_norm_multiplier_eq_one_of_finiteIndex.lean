-- Prove2me | Theorems.Thm_ModularCurve_exists_eq_const_of_norm_multiplier_eq_one_of_finiteIndex
-- name    : ModularCurve.exists_eq_const_of_norm_multiplier_eq_one_of_finiteIndex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/16fac682-7a51-50fa-9ca4-504a01b03dd7
-- title:
--   Unitary multiplier and nonzero cusp limits force constancy
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$ of finite index, let $F : \mathfrak{H} \to \mathbb{C}$ be a function on the upper half-plane, and let $\chi : \Gamma \to \mathbb{C}$ be an arbitrary function (no multiplicativity is assumed). Assume: (i) the function $z \mapsto F(z)$, read on the open set $\{z \in \mathbb{C} : \operatorname{Im} z > 0\}$ via the canonical map $\mathbb{C} \to \mathfrak{H}$, is complex differentiable on that set; (ii) for every $\gamma \in \Gamma$ and every $\tau \in \mathfrak{H}$ one has $F(\gamma \cdot \tau) = \chi(\gamma) F(\tau)$, where the action is the usual action of $\mathrm{SL}_2(\mathbb{Z})$ on $\mathfrak{H}$ by fractional linear transformations; (iii) $\lVert \chi(\gamma) \rVert = 1$ for all $\gamma \in \Gamma$; and (iv) for every $\sigma \in \mathrm{SL}_2(\mathbb{Z})$ there is a nonzero $L \in \mathbb{C}$ such that $F(\sigma \cdot \tau) \to L$ along the filter of points of $\mathfrak{H}$ with imaginary part tending to infinity. The conclusion is that $F$ is constant: there exists $C \in \mathbb{C}$ with $F(\tau) = C$ for all $\tau \in \mathfrak{H}$.
--
--   This is the standard rigidity statement that a holomorphic function on $\mathfrak{H}$ whose modulus is invariant under a finite-index subgroup of $\mathrm{SL}_2(\mathbb{Z})$ and which has finite nonzero limits at all cusps descends to a continuous function on a compact modular curve and hence is constant. It is used in the construction of the complex-place dictionary for $\Gamma_H$-level modular curves, to show that a multiplier character of absolute value one is trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_eq_const_of_norm_multiplier_eq_one_of_finiteIndex.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.exists_eq_const_of_norm_multiplier_eq_one_of_finiteIndex
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (F : ℍ → ℂ) (χ : Γ → ℂ)
    (hF : DifferentiableOn ℂ (fun z : ℂ => F (ofComplex z)) {z : ℂ | 0 < z.im})
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ)
    (hunit : ∀ γ : Γ, ‖χ γ‖ = 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ C : ℂ, ∀ τ : ℍ, F τ = C := by sorry
