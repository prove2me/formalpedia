-- Prove2me | Theorems.Thm_ModularCurve_exists_eq_const_of_norm_multiplier_eq_one
-- name    : ModularCurve.exists_eq_const_of_norm_multiplier_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/09c9d886-8320-5b8d-9ca6-16ae20c145fc
-- title:
--   Unitary multiplier with non-zero cusp limits forces constancy
-- statement:
--   Let $N$ be a non-zero natural number, let $F\colon \mathfrak H \to \mathbb C$ be a function on the upper half plane and let $\chi\colon \Gamma_0(N) \to \mathbb C$ be an arbitrary function on the congruence subgroup $\Gamma_0(N) \subset \mathrm{SL}_2(\mathbb Z)$ (no multiplicativity of $\chi$ is assumed). Assume: (1) the composite $z \mapsto F(\mathrm{ofComplex}\,z)$, where $\mathrm{ofComplex}$ is the canonical section sending a complex number of positive imaginary part to the corresponding point of $\mathfrak H$, is complex differentiable on the open half plane $\{z \in \mathbb C : 0 < \operatorname{Im} z\}$; (2) $F(\gamma \cdot \tau) = \chi(\gamma)\, F(\tau)$ for every $\gamma \in \Gamma_0(N)$, acting through its image in $\mathrm{SL}_2(\mathbb Z)$, and every $\tau \in \mathfrak H$; (3) $\lVert \chi(\gamma)\rVert = 1$ for every $\gamma \in \Gamma_0(N)$; (4) for every $\sigma \in \mathrm{SL}_2(\mathbb Z)$ there is a complex number $L \neq 0$ with $F(\sigma \cdot \tau) \to L$ along the filter $\mathrm{atImInfty}$ on $\mathfrak H$, i.e. as $\operatorname{Im}\tau \to \infty$. The conclusion is that there exists $C \in \mathbb C$ with $F(\tau) = C$ for all $\tau \in \mathfrak H$.
--
--   This is the uniqueness statement for multiplicative holomorphic functions on $X_0(N)$ with unitary multiplier system: such a function, if it has finite non-zero limits at every cusp, is a constant, so the multiplier is trivial. It is used to show that the multiplier attached to a unitarily normalised automorphic unit is $1$ once its norm is $1$ and the relevant Abel–Jacobi class lies in the period lattice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_eq_const_of_norm_multiplier_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.exists_eq_const_of_norm_multiplier_eq_one
    {N : ℕ} [NeZero N] (F : ℍ → ℂ) (χ : CongruenceSubgroup.Gamma0 N → ℂ)
    (hF : DifferentiableOn ℂ (fun z : ℂ => F (ofComplex z)) {z : ℂ | 0 < z.im})
    (hχ : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ)
    (hunit : ∀ γ : CongruenceSubgroup.Gamma0 N, ‖χ γ‖ = 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ C : ℂ, ∀ τ : ℍ, F τ = C := by sorry
