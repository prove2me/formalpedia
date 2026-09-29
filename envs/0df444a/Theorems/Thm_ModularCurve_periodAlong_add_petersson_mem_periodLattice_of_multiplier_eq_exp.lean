-- Prove2me | Theorems.Thm_ModularCurve_periodAlong_add_petersson_mem_periodLattice_of_multiplier_eq_exp
-- name    : ModularCurve.periodAlong_add_petersson_mem_periodLattice_of_multiplier_eq_exp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/ef4fba8b-8cb5-5d86-83c9-4096596bdc50
-- title:
--   Abel's theorem with Petersson correction on Γ₀(N)
-- statement:
--   Fix $N\ge 1$ and write $\Gamma=\Gamma_0(N)\subset SL_2(\mathbb Z)$. Let $c:\mathbb H\to\mathbb Z$ be finitely supported, let $F:\mathbb H\to\mathbb C$ be a function and let $k$ be a cusp form of weight $2$ on $\Gamma$. Assume: (i) the function $z\mapsto F(\mathrm{ofComplex}\,z)$ on $\mathbb C$ is meromorphic at every point $\tau\in\mathbb H$; (ii) for all $\gamma\in\Gamma$ and $\tau\in\mathbb H$, $F(\gamma\tau)=\exp\bigl(2\pi i\,\mathrm{Re}\,P_\gamma(k)\bigr)F(\tau)$, where $P_\gamma=$ [`ModularCurve.period N γ`](def/ModularCurve_PeriodLattice.html#L92) is the functional $g\mapsto\int_0^1 g(\text{segment from }i\text{ to }\gamma i\text{ at }t)\,(\gamma i-i)\,dt$, i.e. integration of $g(z)\,dz$ along the straight segment from $i$ to $\gamma\cdot i$; (iii) for every $\sigma\in SL_2(\mathbb Z)$ there is $L\ne 0$ with $F(\sigma\tau)\to L$ as $\mathrm{Im}\,\tau\to\infty$; (iv) for every $\tau\in\mathbb H$ the meromorphic order $n$ of $F$ at $\tau$ is a (finite) integer and $2n=\#\mathrm{Stab}_\Gamma(\tau)\cdot\sum_{\tau'}c(\tau')$, the sum running over the points $\tau'$ in the support of $c$ lying in the $\Gamma$-orbit of $\tau$. Then there exists $\Lambda$ in the period lattice of level $N$, the $\mathbb Z$-span of the functionals $P_\gamma$ ($\gamma\in\Gamma$) inside the $\mathbb C$-dual of the space of weight-$2$ cusp forms on $\Gamma$, such that for every weight-$2$ cusp form $g$ on $\Gamma$,
--   $$\sum_{\tau}c(\tau)\int_i^{\tau}g(z)\,dz\;+\;i\int_{\mathcal F_N}\mathrm{petersson}_2(k,g)(\tau)\;=\;\Lambda(g),$$
--   the first integrals being along straight segments and $\mathcal F_N=\bigcup_{q\in SL_2(\mathbb Z)/\Gamma}(\mathrm{Quotient.out}\,q)^{-1}\cdot\mathcal D$ the union of translates of the standard closed fundamental domain $\mathcal D$ of $SL_2(\mathbb Z)$ over coset representatives.
--
--   This is the necessity half of an Abel-type reciprocity law on the modular curve of level $N$: a multiplicative function with the multiplier $\exp(2\pi i\,\mathrm{Re}\int_i^{\gamma i}k)$ and divisor $c$ forces the Abel–Jacobi functional of $c$, corrected by $i$ times the weight-$2$ Petersson pairing against $k$, to lie in the period lattice. It is proved by combining a chain-level vanishing statement for such $F$ with the fact that sums of segment periods along a cycle with zero boundary lie in the period lattice, and it is used by [`ModularCurve.multiplier_eq_exp_of_periodAlong_add_petersson_mem_periodLattice`](thm.html#ModularCurve.multiplier_eq_exp_of_periodAlong_add_petersson_mem_periodLattice), the converse implication.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_periodAlong_add_petersson_mem_periodLattice_of_multiplier_eq_exp.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology

open Classical in

theorem ModularCurve.periodAlong_add_petersson_mem_periodLattice_of_multiplier_eq_exp
    {N : ℕ} [NeZero N] (c : UpperHalfPlane →₀ ℤ)
    (F : ℍ → ℂ) (k : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.period N γ k).re : ℂ)) * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (hord : ∀ τ : ℍ, ∃ n : ℤ,
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (n : WithTop ℤ) ∧
        2 * n = (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) : ℤ) *
          c.sum (fun τ' m =>
            if ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • τ' = τ then m else 0)) :
    ∃ Λ ∈ ModularCurve.periodLattice N, ∀ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
      (c.sum fun τ n => n • ModularCurve.periodAlong N UpperHalfPlane.I τ) g +
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
          (CongruenceSubgroup.Gamma0 N), UpperHalfPlane.petersson 2 k g τ) = Λ g := by sorry
