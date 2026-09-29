-- Prove2me | Theorems.Thm_ModularCurve_exists_meromorphic_smul_eq_mul_of_slashInvariant_residue
-- name    : ModularCurve.exists_meromorphic_smul_eq_mul_of_slashInvariant_residue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/2a5242df-c05f-5d6b-858a-93466c406173
-- title:
--   Exponentiating an invariant differential of the third kind on H
-- statement:
--   Let $\Gamma$ be an arbitrary subgroup of $\mathrm{SL}_2(\mathbb Z)$, let $m:\mathfrak H\to\mathbb Z$ be an arbitrary function on the upper half plane and let $\omega:\mathfrak H\to\mathbb C$. Assume three things. First, $\omega\mid_2\gamma=\omega$ for every $\gamma\in\Gamma$, the slash being the weight-$2$ one. Second, decay at every cusp: for each $\sigma\in\mathrm{SL}_2(\mathbb Z)$ there is $\delta>0$ with $(\omega\mid_2\sigma)(\tau)=O\bigl(e^{-\delta\,\mathrm{Im}\,\tau}\bigr)$ along the filter `atImInfty`. Third, at each $\tau\in\mathfrak H$ there is a function $g$ on $\mathbb C$, analytic at $\tau$, such that $\omega(\mathrm{ofComplex}\,z)=m(\tau)/(z-\tau)+g(z)$ for all $z$ in a punctured neighbourhood of $\tau$, and $\omega(\tau)=g(\tau)$ whenever $m(\tau)=0$; here `ofComplex` is the map from $\mathbb C$ to $\mathfrak H$ inverting the inclusion on the upper half plane. The conclusion asserts the existence of $F:\mathfrak H\to\mathbb C$ and $\chi:\Gamma\to\mathbb C$ such that: $z\mapsto F(\mathrm{ofComplex}\,z)$ is meromorphic at every point of $\mathfrak H$; $F(\gamma\tau)=\chi(\gamma)F(\tau)$ for all $\gamma\in\Gamma$ and $\tau\in\mathfrak H$; for every $\sigma\in\mathrm{SL}_2(\mathbb Z)$ the function $\tau\mapsto F(\sigma\tau)$ converges along `atImInfty` to some limit $L\neq 0$; and the meromorphic order of $z\mapsto F(\mathrm{ofComplex}\,z)$ at each $\tau\in\mathfrak H$ equals $m(\tau)$ in $\mathbb Z\cup\{\infty\}$. No finiteness hypothesis on the index of $\Gamma$, and no constraint on $m$ beyond the residue condition, is imposed; $\chi$ is produced as a function on $\Gamma$, with no multiplicativity asserted.
--
--   This is the complex-analytic half of the sufficiency direction of Abel's theorem, stated on the simply connected cover $\mathfrak H$: a differential of the third kind with integral residues, invariant in weight $2$ and decaying at the cusps, integrates and exponentiates to a multiplicative meromorphic function with prescribed divisor and non-zero limits at every cusp. It rests on the construction of a meromorphic primitive with prescribed orders and logarithmic derivative $\omega$ ([`ModularCurve.exists_meromorphic_logDeriv_eq_of_int_residue`](thm.html#ModularCurve.exists_meromorphic_logDeriv_eq_of_int_residue)), and is used in the Abel–Jacobi computations that identify when a divisor class on a modular curve is trivial, i.e. when the Abel–Jacobi image lies in the relevant period lattice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_meromorphic_smul_eq_mul_of_slashInvariant_residue.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups Topology ModularForm

theorem ModularCurve.exists_meromorphic_smul_eq_mul_of_slashInvariant_residue
    (Γ : Subgroup SL(2, ℤ)) (m : ℍ → ℤ) (ω : ℍ → ℂ)
    (hΓ : ∀ γ ∈ Γ, ω ∣[(2 : ℤ)] γ = ω)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ δ : ℝ, 0 < δ ∧
      (ω ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im))
    (hres : ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      (∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = (m τ : ℂ) / (z - τ) + g z) ∧
      (m τ = 0 → ω τ = g τ)) :
    ∃ (F : ℍ → ℂ) (χ : Γ → ℂ),
      (∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)) ∧
      (∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ) ∧
      (∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
        Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) ∧
      ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (m τ : WithTop ℤ) := by sorry
