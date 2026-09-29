-- Prove2me | Theorems.Thm_ModularCurve_exists_invariant_untwist_of_multiplier_eq_exp_periodOf
-- name    : ModularCurve.exists_invariant_untwist_of_multiplier_eq_exp_periodOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/29fe0733-ef92-5dd1-819d-b2a02f5c7636
-- title:
--   Untwisting a unitary multiplier into a Γ-invariant C¹ function
-- statement:
--   Let $\Gamma$ be a finite-index subgroup of $\mathrm{SL}_2(\mathbb{Z})$, let $F:\mathfrak{H}\to\mathbb{C}$ be a function and let $k$ be a weight-two cusp form on $\Gamma$. Assume: (i) the transported function $z\mapsto F(\mathrm{ofComplex}\,z)$ on $\mathbb{C}$ is meromorphic at every point $\tau$ of the upper half-plane; (ii) for every $\gamma\in\Gamma$ and every $\tau$, $F(\gamma\tau)=e^{2\pi i\,\mathrm{Re}\,P_\gamma(k)}F(\tau)$, where $P_\gamma=$ [`ModularCurve.periodOf`](def/ModularCurve_PeriodOf.html#L56) $\Gamma\,\gamma$ is the linear functional on weight-two cusp forms given by the period integral $\int_0^1$ of the period integrand along the path from $i$ to $\gamma i$, evaluated at $k$; (iii) for every $\sigma\in\mathrm{SL}_2(\mathbb{Z})$ the function $\tau\mapsto F(\sigma\tau)$ tends, as $\mathrm{Im}\,\tau\to\infty$, to a non-zero limit. Then there exists $\Phi:\mathbb{C}\to\mathbb{C}$ such that: near each $\tau\in\mathfrak{H}$, $\Phi(z)=(z-\tau)^{n_\tau}\Psi(z)$ for some $\Psi$ that is $C^1$ over $\mathbb{R}$ at $\tau$ with $\Psi(\tau)\neq 0$, where $n_\tau$ is the integer underlying the meromorphic order of $F$ at $\tau$; $\Phi(\gamma\tau)=\Phi(\tau)$ for all $\gamma\in\Gamma$, $\tau\in\mathfrak{H}$; for every $\sigma\in\mathrm{SL}_2(\mathbb{Z})$, $\Phi\circ\sigma$ tends to a non-zero limit and its real Fréchet derivative tends to $0$ at $i\infty$; and for almost every $z$ with $\mathrm{Im}\,z>0$, $\Phi(z)\neq0$, $\Phi$ is real-differentiable at $z$, and $$\mathrm{d}\Phi_z(1)=\Phi(z)\Big(\frac{F'}{F}(z)-2\pi i\,\mathrm{Re}\,k(z)\Big),\qquad \mathrm{d}\Phi_z(i)=\Phi(z)\Big(i\frac{F'}{F}(z)+2\pi i\,\mathrm{Im}\,k(z)\Big).$$
--
--   This is the untwisting step in the Abel-type reciprocity for modular curves: a multiplicatively automorphic meromorphic function with unitary multiplier $e^{2\pi i\,\mathrm{Re}\,P_\gamma(k)}$ is replaced by the genuinely $\Gamma$-invariant function $\Phi=F\cdot\exp(-2\pi i\,\mathrm{Re}\int_i^\tau k)$, which has the same divisor but is only $C^1$ rather than holomorphic, together with control at all cusps. It is stated for an arbitrary finite-index $\Gamma\le\mathrm{SL}_2(\mathbb{Z})$ and is used in the computation of the period-lattice relation [`ModularCurve.exists_mem_periodLatticeOf_sum_periodAlongOf_add_petersson_eq_of_multiplier_eq_exp`](thm.html#ModularCurve.exists_mem_periodLatticeOf_sum_periodAlongOf_add_petersson_eq_of_multiplier_eq_exp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_invariant_untwist_of_multiplier_eq_exp_periodOf.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open UpperHalfPlane Filter
open scoped MatrixGroups Topology

theorem ModularCurve.exists_invariant_untwist_of_multiplier_eq_exp_periodOf
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (F : ℍ → ℂ) (k : CuspForm (Γ) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.periodOf Γ γ k).re : ℂ)) * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ Φ : ℂ → ℂ,
      (∀ τ : ℍ, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ (τ : ℂ) ∧ Ψ τ ≠ 0 ∧
        Φ =ᶠ[𝓝 (τ : ℂ)] fun z =>
          (z - τ) ^ ((meromorphicOrderAt (fun w : ℂ => F (ofComplex w)) (τ : ℂ)).untop₀ : ℤ) *
            Ψ z) ∧
      (∀ (γ : Γ) (τ : ℍ), Φ (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = Φ τ) ∧
      (∀ σ : SL(2, ℤ), ∃ c : ℂ, c ≠ 0 ∧
        Tendsto (fun τ : ℍ => Φ ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 c)) ∧
      (∀ σ : SL(2, ℤ), Tendsto (fun τ : ℍ =>
        fderiv ℝ (fun u : ℂ => Φ ((σ • ofComplex u : ℍ) : ℂ)) (τ : ℂ)) atImInfty (𝓝 0)) ∧
      (∀ᵐ z : ℂ, 0 < z.im → Φ z ≠ 0 ∧ DifferentiableAt ℝ Φ z ∧
        fderiv ℝ Φ z 1 = Φ z *
          (deriv (fun w : ℂ => F (ofComplex w)) z / F (ofComplex z) -
            2 * Real.pi * Complex.I * ((k (ofComplex z)).re : ℂ)) ∧
        fderiv ℝ Φ z Complex.I = Φ z *
          (Complex.I * (deriv (fun w : ℂ => F (ofComplex w)) z / F (ofComplex z)) +
            2 * Real.pi * Complex.I * ((k (ofComplex z)).im : ℂ))) := by sorry
