-- Prove2me | Theorems.Thm_ModularCurve_exists_invariant_untwist_of_multiplier_eq_exp
-- name    : ModularCurve.exists_invariant_untwist_of_multiplier_eq_exp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/ddace8a6-751a-5d91-8e7e-f199a0837c80
-- title:
--   Untwisting a unitary multiplier to a Γ₀(N)-invariant function
-- statement:
--   Let $N \geq 1$, let $F : \mathbb{H} \to \mathbb{C}$ be a function on the upper half plane and let $k$ be a cusp form of weight $2$ for $\Gamma_0(N)$. Assume: (i) for every $\tau \in \mathbb{H}$ the function $z \mapsto F(\mathrm{ofComplex}\, z)$ is meromorphic at $\tau$; (ii) $F$ transforms multiplicatively under $\Gamma_0(N)$ with the unitary multiplier given by the real part of the period of $k$, namely $F(\gamma \cdot \tau) = \exp\bigl(2\pi i \,\operatorname{Re}(\mathrm{period}\,N\,\gamma)(k)\bigr) F(\tau)$ for all $\gamma \in \Gamma_0(N)$ and $\tau \in \mathbb{H}$, where $(\mathrm{period}\,N\,\gamma)(k)$ is the line integral of $k$ along the path from $i$ to $\gamma \cdot i$ (the value at $k$ of the linear functional [`ModularCurve.periodAlong N UpperHalfPlane.I ((γ : SL(2,ℤ)) • UpperHalfPlane.I)`](def/ModularCurve_PeriodLattice.html#L78), defined as $\int_0^1 \mathrm{periodIntegrand}\,N\,i\,(\gamma \cdot i)\,k\,t\,dt$); (iii) for every $\sigma \in SL_2(\mathbb{Z})$ the function $\tau \mapsto F(\sigma \cdot \tau)$ tends to some non-zero limit as $\operatorname{Im}\tau \to \infty$. Then there exists $\Phi : \mathbb{C} \to \mathbb{C}$ such that: (1) near each $\tau \in \mathbb{H}$ one has $\Phi(z) = (z-\tau)^{n_\tau}\Psi(z)$ on a neighbourhood of $\tau$, where $n_\tau$ is the integer obtained from the meromorphic order of $z \mapsto F(\mathrm{ofComplex}\, z)$ at $\tau$ via `untop₀` and $\Psi$ is real-$C^1$ at $\tau$ with $\Psi(\tau) \neq 0$; (2) $\Phi(\gamma \cdot \tau) = \Phi(\tau)$ for all $\gamma \in \Gamma_0(N)$, $\tau \in \mathbb{H}$; (3) for every $\sigma \in SL_2(\mathbb{Z})$, $\tau \mapsto \Phi(\sigma\cdot\tau)$ tends to a non-zero limit as $\operatorname{Im}\tau \to \infty$; (4) for every $\sigma \in SL_2(\mathbb{Z})$, the real Fréchet derivative of $u \mapsto \Phi(\sigma \cdot \mathrm{ofComplex}\, u)$ at $\tau$ tends to $0$ as $\operatorname{Im}\tau \to \infty$; and (5) for almost every $z \in \mathbb{C}$ with $\operatorname{Im} z > 0$: $\Phi(z) \neq 0$, $\Phi$ is real-differentiable at $z$, and the directional derivatives in the directions $1$ and $i$ are $\Phi(z)\bigl(F'/F(z) - 2\pi i \operatorname{Re} k(z)\bigr)$ and $\Phi(z)\bigl(i\,F'/F(z) + 2\pi i \operatorname{Im} k(z)\bigr)$ respectively, where $F'/F$ is formed from $\mathrm{deriv}$ of $z \mapsto F(\mathrm{ofComplex}\,z)$; that is, $d\Phi/\Phi = dF/F - 2\pi i\,\operatorname{Re}(k\,dz)$.
--
--   This is the standard passage from a multiplicative automorphic function with a unitary multiplier system to a genuinely $\Gamma_0(N)$-invariant, merely real-differentiable function with the same divisor, the twist being by $\exp(-2\pi i \operatorname{Re}\int_i^z k)$, whose multiplier cancels that of $F$ by the cocycle relation $\operatorname{Re}\int_i^{\gamma\tau} k = \operatorname{Re}\int_i^{\tau} k + \operatorname{Re}\int_i^{\gamma i} k$. It feeds the analysis of the period lattice of weight-two cusp forms on $\Gamma_0(N)$, being used in [`ModularCurve.exists_mem_periodLattice_sum_periodAlong_add_petersson_eq_of_multiplier_eq_exp`](thm.html#ModularCurve.exists_mem_periodLattice_sum_periodAlong_add_petersson_eq_of_multiplier_eq_exp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_invariant_untwist_of_multiplier_eq_exp.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane Filter
open scoped MatrixGroups Topology

theorem ModularCurve.exists_invariant_untwist_of_multiplier_eq_exp
    {N : ℕ} [NeZero N]
    (F : ℍ → ℂ) (k : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.period N γ k).re : ℂ)) * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ Φ : ℂ → ℂ,
      (∀ τ : ℍ, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ (τ : ℂ) ∧ Ψ τ ≠ 0 ∧
        Φ =ᶠ[𝓝 (τ : ℂ)] fun z =>
          (z - τ) ^ ((meromorphicOrderAt (fun w : ℂ => F (ofComplex w)) (τ : ℂ)).untop₀ : ℤ) *
            Ψ z) ∧
      (∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), Φ (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = Φ τ) ∧
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
