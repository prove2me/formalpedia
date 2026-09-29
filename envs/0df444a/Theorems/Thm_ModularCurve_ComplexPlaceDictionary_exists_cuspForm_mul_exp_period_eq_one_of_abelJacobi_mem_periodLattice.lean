-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionary_exists_cuspForm_mul_exp_period_eq_one_of_abelJacobi_mem_periodLattice
-- name    : ModularCurve.ComplexPlaceDictionary.exists_cuspForm_mul_exp_period_eq_one_of_abelJacobi_mem_periodLattice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/737aabad-a42c-568d-a471-e54ee44e9696
-- title:
--   Multiplier of a multiplicative meromorphic function is a period exponential
-- statement:
--   Let $N\ge 1$ and let $D$ be a complex place dictionary at level $N$: a map $\tau\mapsto P_\tau$ from the upper half-plane $\mathfrak H$ to the places of $\mathbb C$-function field `laurentBaseChange ℂ (modularFunctionFieldFull N)`, together with ramification indices $e_\tau\ge 1$, such that $P_{\gamma\tau}=P_\tau$ for $\gamma\in\Gamma_0(N)$, such that an element $x$ of the field lies in the valuation subring of $P_\tau$ exactly when $z\mapsto\|\mathrm{realize}_N(x)(z)\|$ is bounded near $\tau$ on punctured neighbourhoods, and such that for $x\neq 0$ the meromorphic order of $\mathrm{realize}_N(x)$ at $\tau$ equals $e_\tau\cdot\operatorname{ord}_{P_\tau}(x)$. Let $c:\mathfrak H\to\mathbb Z$ be finitely supported, with pushforward divisor $D_*(c)=\sum_\tau c(\tau)P_\tau$ of degree $0$ (degree being the additive map weighting each place by its degree), and assume the functional $\sum_\tau c(\tau)\,\mathrm{periodAlong}_N(i,\tau)$ on weight-$2$ cusp forms for $\Gamma_0(N)$ — integration of $f$ along the geodesic segment from $i$ to $\tau$ — lies in the period lattice, the $\mathbb Z$-span of the functionals $\mathrm{periodAlong}_N(i,\gamma i)$, $\gamma\in\Gamma_0(N)$. Let $F:\mathfrak H\to\mathbb C$ and $\chi:\Gamma_0(N)\to\mathbb C$ satisfy: $F$ (transported to $\mathbb C$ via `ofComplex`) is meromorphic at every point of $\mathfrak H$; $F(\gamma\tau)=\chi(\gamma)F(\tau)$ for all $\gamma\in\Gamma_0(N)$, $\tau\in\mathfrak H$; for every $\sigma\in\mathrm{SL}_2(\mathbb Z)$ the function $\tau\mapsto F(\sigma\tau)$ tends to some non-zero limit as $\operatorname{Im}\tau\to\infty$; and the meromorphic order of $F$ at each $\tau$ equals $e_\tau$ times the coefficient of $D_*(c)$ at $P_\tau$. Then there is a cusp form $f$ of weight $2$ for $\Gamma_0(N)$ with $\chi(\gamma)\exp\bigl(\mathrm{period}_N(\gamma)(f)\bigr)=1$ for every $\gamma\in\Gamma_0(N)$.
--
--   This is the reciprocity step in the sufficiency direction of Abel's theorem for the compact Riemann surface $X_0(N)(\mathbb C)$: a multiplicative meromorphic function whose divisor has Abel–Jacobi image in the period lattice has multiplier system given by the exponentials of the periods of a weight-$2$ cusp form. It feeds into the construction of a genuine meromorphic function with prescribed divisor, [`ModularCurve.ComplexPlaceDictionary.exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLattice`](thm.html#ModularCurve.ComplexPlaceDictionary.exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLattice).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionary_exists_cuspForm_mul_exp_period_eq_one_of_abelJacobi_mem_periodLattice.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_ModularCurve_PeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.ComplexPlaceDictionary.exists_cuspForm_mul_exp_period_eq_one_of_abelJacobi_mem_periodLattice
    {N : ℕ} [NeZero N] (D : ModularCurve.ComplexPlaceDictionary N) (c : UpperHalfPlane →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0)
    (hΛ : (c.sum fun τ n => n • ModularCurve.periodAlong N UpperHalfPlane.I τ) ∈
      ModularCurve.periodLattice N)
    (F : ℍ → ℂ) (χ : CongruenceSubgroup.Gamma0 N → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (hord : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) =
      (((D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ) : ℤ) : WithTop ℤ)) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
      ∀ γ : CongruenceSubgroup.Gamma0 N, χ γ * Complex.exp (ModularCurve.period N γ f) = 1 := by sorry
