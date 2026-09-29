-- Prove2me | Theorems.Thm_ModularCurve_exists_cuspForm_multiplier_eq_exp_periodOf_of_norm_eq_one
-- name    : ModularCurve.exists_cuspForm_multiplier_eq_exp_periodOf_of_norm_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/782b1326-2a83-558e-8c94-3e40b9c22692
-- title:
--   Unitary multipliers as exponentials of real cusp-form periods
-- statement:
--   Let $\Gamma\le SL(2,\mathbb{Z})$ be a subgroup of finite index with $-1\in\Gamma$ which is a congruence subgroup in the sense of `CongruenceSubgroup.IsCongruenceSubgroup`, let $c:\mathcal{H}\to\mathbb{Z}$ be a finitely supported function on the upper half-plane, let $F:\mathcal{H}\to\mathbb{C}$ and let $\chi:\Gamma\to\mathbb{C}$. Assume: (i) for every $\tau\in\mathcal{H}$ the function $z\mapsto F(\mathrm{ofComplex}\,z)$ is meromorphic at $\tau$; (ii) $F(\gamma\tau)=\chi(\gamma)F(\tau)$ for all $\gamma\in\Gamma$, $\tau\in\mathcal{H}$; (iii) $\|\chi(\gamma)\|=1$ for all $\gamma\in\Gamma$; (iv) for every $\sigma\in SL(2,\mathbb{Z})$ the function $\tau\mapsto F(\sigma\tau)$ tends, along the filter $\mathrm{atImInfty}$, to some nonzero limit $L\in\mathbb{C}$; (v) for every $\tau\in\mathcal{H}$ the meromorphic order of $z\mapsto F(\mathrm{ofComplex}\,z)$ at $\tau$ is a (finite) integer $n$ satisfying $2n=\#\mathrm{Stab}_\Gamma(\tau)\cdot\sum_{\tau'}c(\tau')$, the sum being over the support of $c$ with the convention that $\tau'$ contributes $c(\tau')$ when $\tau'$ lies in the $\Gamma$-orbit of $\tau$ and $0$ otherwise. The conclusion is that there exists a cusp form $k$ of weight $2$ for $\Gamma$ such that for every $\gamma\in\Gamma$ one has $\chi(\gamma)=\exp\bigl(2\pi i\,\mathrm{Re}\,(\mathrm{periodOf}\,\Gamma\,\gamma)(k)\bigr)$, where $(\mathrm{periodOf}\,\Gamma\,\gamma)$ is the linear functional on weight-$2$ cusp forms obtained by integrating `periodIntegrandOf` over $t\in[0,1]$, i.e. the period integral from $i$ to $\gamma i$.
--
--   This is the multiplicative form of surjectivity in the real Eichler–Shimura theory: the argument of a unitary multiplier system whose associated meromorphic function has nonzero finite limits at all cusps and divisor prescribed orbit-by-orbit is realised as the real part of the period map of a weight-$2$ cusp form. It is applied in [`ModularCurve.multiplier_eq_exp_of_periodAlongOf_add_petersson_mem_periodLatticeOf`](thm.html#ModularCurve.multiplier_eq_exp_of_periodAlongOf_add_petersson_mem_periodLatticeOf), and rests on injectivity of $k\mapsto\mathrm{Re}\int k$ together with the bound on the rank of real parabolic homomorphisms by twice $\dim_{\mathbb{C}}S_2(\Gamma)$, the latter being where the congruence hypothesis enters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_cuspForm_multiplier_eq_exp_periodOf_of_norm_eq_one.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology
open Classical in

theorem ModularCurve.exists_cuspForm_multiplier_eq_exp_periodOf_of_norm_eq_one
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ) (c : UpperHalfPlane →₀ ℤ)
    (F : ℍ → ℂ) (χ : Γ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ)
    (hunit : ∀ γ : Γ, ‖χ γ‖ = 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (hord : ∀ τ : ℍ, ∃ n : ℤ,
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (n : WithTop ℤ) ∧
        2 * n = (Nat.card (MulAction.stabilizer Γ τ) : ℤ) *
          c.sum (fun τ' m =>
            if ∃ γ : Γ, (γ : SL(2, ℤ)) • τ' = τ then m else 0)) :
    ∃ k : CuspForm Γ 2, ∀ γ : Γ,
      χ γ = Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.periodOf Γ γ k).re : ℂ)) := by sorry
