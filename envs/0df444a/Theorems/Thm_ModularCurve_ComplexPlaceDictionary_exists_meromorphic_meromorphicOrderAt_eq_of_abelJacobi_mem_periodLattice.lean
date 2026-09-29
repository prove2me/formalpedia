-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionary_exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLattice
-- name    : ModularCurve.ComplexPlaceDictionary.exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLattice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/446204c4-22ab-5cfa-9663-a3d9ab12f6fc
-- title:
--   Abel's theorem for X₀(N): analytic sufficiency half
-- statement:
--   Fix $N\ge 1$ and a complex place dictionary $D$ at level $N$, that is: a map $\tau\mapsto D.\mathrm{pt}(\tau)$ from $\mathfrak H$ to the places of the field $\mathbb C F_N =$ `laurentBaseChange ℂ (modularFunctionFieldFull N)` together with positive integers $D.\mathrm{ramification}(\tau)$, such that $D.\mathrm{pt}$ is invariant under $\Gamma_0(N)$, an element $x$ of $\mathbb C F_N$ lies in the valuation subring of $D.\mathrm{pt}(\tau)$ exactly when the norm of its realisation `realize N x` is bounded near $\tau$ on the punctured neighbourhood filter, and for $x\ne 0$ the meromorphic order at $\tau$ of $z\mapsto$ `realize N x (ofComplex z)` equals $D.\mathrm{ramification}(\tau)\cdot\operatorname{ord}_{D.\mathrm{pt}(\tau)}(x)$. Let $c:\mathfrak H\to_{\mathrm f}\mathbb Z$ be finitely supported, assume the divisor $\mathrm{mapDomain}\,D.\mathrm{pt}\,c$ has degree $0$ (the $\mathbb Z$-linear extension of $v\mapsto \deg v$), and assume the functional $\sum_\tau c(\tau)\cdot$ `periodAlong N I τ` — integration of weight-$2$ cusp forms on $\Gamma_0(N)$ along the segment from $i$ to $\tau$ — lies in `periodLattice N`, the $\mathbb Z$-span of the functionals `period N γ` for $\gamma\in\Gamma_0(N)$. Then there is $F:\mathfrak H\to\mathbb C$ such that: $z\mapsto F(\mathrm{ofComplex}\,z)$ is meromorphic at every point of $\mathfrak H$; $F(\gamma\cdot\tau)=F(\tau)$ for all $\gamma\in\Gamma_0(N)$; for every $\sigma\in SL(2,\mathbb Z)$ the function $\tau\mapsto F(\sigma\cdot\tau)$ tends to a nonzero limit as $\operatorname{Im}\tau\to\infty$; and its meromorphic order at each $\tau$ equals $D.\mathrm{ramification}(\tau)\cdot(\mathrm{mapDomain}\,D.\mathrm{pt}\,c)(D.\mathrm{pt}(\tau))$.
--
--   This is the analytic sufficiency half of Abel's theorem for $X_0(N)$, formulated on the upper half plane: a degree-zero divisor supported away from the cusps whose Abel–Jacobi image lies in the period lattice is the divisor of a $\Gamma_0(N)$-invariant meromorphic function that is a unit at every cusp. It is used to prove [`ModularCurve.ComplexPlaceDictionary.isPrincipal_of_abelJacobi_mem_periodLattice`](thm.html#ModularCurve.ComplexPlaceDictionary.isPrincipal_of_abelJacobi_mem_periodLattice), the principality statement in the divisor class group of the modular function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionary_exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLattice.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_ModularCurve_PeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.ComplexPlaceDictionary.exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLattice
    {N : ℕ} [NeZero N] (D : ModularCurve.ComplexPlaceDictionary N) (c : UpperHalfPlane →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0)
    (hΛ : (c.sum fun τ n => n • ModularCurve.periodAlong N UpperHalfPlane.I τ) ∈
      ModularCurve.periodLattice N) :
    ∃ F : ℍ → ℂ,
      (∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)) ∧
      (∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ τ : ℍ, F (γ • τ) = F τ) ∧
      (∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
        Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) ∧
      ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) =
        (((D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ) : ℤ) : WithTop ℤ) := by sorry
