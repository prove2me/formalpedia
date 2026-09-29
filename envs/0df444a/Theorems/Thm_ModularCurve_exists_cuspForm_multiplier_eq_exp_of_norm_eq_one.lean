-- Prove2me | Theorems.Thm_ModularCurve_exists_cuspForm_multiplier_eq_exp_of_norm_eq_one
-- name    : ModularCurve.exists_cuspForm_multiplier_eq_exp_of_norm_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/067a5f96-2b74-5564-9380-24a6d735595f
-- title:
--   Unitary multipliers are exponentials of weight-2 periods
-- statement:
--   Fix $N \ge 1$, a finitely supported function $c : \mathbb{H} \to \mathbb{Z}$, a function $F : \mathbb{H} \to \mathbb{C}$ and a function $\chi$ on $\Gamma_0(N)$ with complex values. Assume: (i) for every $\tau \in \mathbb{H}$ the function $z \mapsto F(\mathrm{ofComplex}\,z)$ on $\mathbb{C}$ is meromorphic at the point $\tau$; (ii) $F(\gamma\tau) = \chi(\gamma)F(\tau)$ for all $\gamma \in \Gamma_0(N)$ and $\tau \in \mathbb{H}$; (iii) $\lVert\chi(\gamma)\rVert = 1$ for all $\gamma$; (iv) for every $\sigma \in \mathrm{SL}_2(\mathbb{Z})$ the function $\tau \mapsto F(\sigma\tau)$ tends, along the filter $\operatorname{Im}\tau \to \infty$, to some nonzero limit $L$; and (v) for every $\tau \in \mathbb{H}$ the meromorphic order of $z \mapsto F(\mathrm{ofComplex}\,z)$ at $\tau$ is a (finite) integer $n$ satisfying $2n = \#\mathrm{Stab}_{\Gamma_0(N)}(\tau) \cdot \sum_{\tau'} c(\tau')$, the sum being over the support of $c$ with the terms at points $\tau'$ outside the $\Gamma_0(N)$-orbit of $\tau$ replaced by $0$. Then there is a cusp form $k$ of weight $2$ on $\Gamma_0(N)$ such that for every $\gamma \in \Gamma_0(N)$ one has $\chi(\gamma) = \exp\bigl(2\pi i \,\operatorname{Re}(\mathrm{period}\,N\,\gamma)(k)\bigr)$, where $(\mathrm{period}\,N\,\gamma)(k)$ is the integral over $t \in [0,1]$ of the period integrand of $k$ along the path from $i$ to $\gamma i$, i.e. $\int_i^{\gamma i} k(z)\,dz$.
--
--   This is the classical statement that a unitary multiplier system attached to a meromorphic function on $X_0(N)$ with divisor supported in $\Gamma_0(N)$-orbits and nonzero finite values at the cusps is given by exponentiating the real part of a weight-2 period, the point being that the relevant first homology of $X_0(N)$ is torsion-free. It is used in [`ModularCurve.multiplier_eq_exp_of_periodAlong_add_petersson_mem_periodLattice`](thm.html#ModularCurve.multiplier_eq_exp_of_periodAlong_add_petersson_mem_periodLattice), and is proved by combining the character-theoretic statement [`ModularCurve.exists_addMonoidHom_exp_eq_of_norm_eq_one_of_trace_sq_le_four`](thm.html#ModularCurve.exists_addMonoidHom_exp_eq_of_norm_eq_one_of_trace_sq_le_four) with the realisation of periods as parabolic homomorphisms and the dimension bounds for weight-2 cusp forms on $\Gamma_0(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_cuspForm_multiplier_eq_exp_of_norm_eq_one.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups Topology

open Classical in

theorem ModularCurve.exists_cuspForm_multiplier_eq_exp_of_norm_eq_one
    {N : ℕ} [NeZero N] (c : UpperHalfPlane →₀ ℤ)
    (F : ℍ → ℂ) (χ : CongruenceSubgroup.Gamma0 N → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ)
    (hunit : ∀ γ : CongruenceSubgroup.Gamma0 N, ‖χ γ‖ = 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (hord : ∀ τ : ℍ, ∃ n : ℤ,
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (n : WithTop ℤ) ∧
        2 * n = (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) : ℤ) *
          c.sum (fun τ' m =>
            if ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • τ' = τ then m else 0)) :
    ∃ k : CuspForm (CongruenceSubgroup.Gamma0 N) 2, ∀ γ : CongruenceSubgroup.Gamma0 N,
      χ γ = Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.period N γ k).re : ℂ)) := by sorry
