-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionary_exists_slashInvariant_residue_eq_of_degree_eq_zero
-- name    : ModularCurve.ComplexPlaceDictionary.exists_slashInvariant_residue_eq_of_degree_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/1f513766-255d-568f-a8cd-6c036093bc93
-- title:
--   Weight-two functions with prescribed integral residues on X₀(N)
-- statement:
--   Let $N\ge 1$ and let $D$ be a complex place dictionary at level $N$, that is: a map $\tau\mapsto P_\tau$ from the upper half plane $\mathfrak H$ to the places of the field $\mathbb C F_N=$ `laurentBaseChange ℂ (modularFunctionFieldFull N)` (the subfield of $\mathbb C((X))$ generated over $\mathbb C$ by the image of the field of $q$-expansions `modularFunctionFieldFull N`), together with integers $e_\tau=D.\mathrm{ramification}\,\tau\ge 1$, such that $P_{\gamma\tau}=P_\tau$ for all $\gamma\in\Gamma_0(N)$, such that $x\in\mathbb C F_N$ lies in the valuation subring of $P_\tau$ exactly when $z\mapsto\|\mathrm{realize}\,N\,x\,z\|$ is bounded on a punctured neighbourhood of $\tau$ in $\mathfrak H$, and such that for $x\ne 0$ the meromorphic order of $z\mapsto \mathrm{realize}\,N\,x\,(\mathrm{ofComplex}\,z)$ at $\tau$ equals $e_\tau\cdot\operatorname{ord}_{P_\tau}(x)$. Let $c:\mathfrak H\to\mathbb Z$ be finitely supported, write $D_*(c)=\sum_\tau c(\tau)\,P_\tau$ for its pushforward divisor, and assume its degree $\sum_P D_*(c)(P)\cdot\deg P$ vanishes. Then there is a function $\omega:\mathfrak H\to\mathbb C$ with: (i) $\omega\mid_2\gamma=\omega$ for every $\gamma\in\Gamma_0(N)$; (ii) for every $\sigma\in\mathrm{SL}_2(\mathbb Z)$ there is $\delta>0$ with $\omega\mid_2\sigma=O(e^{-\delta\,\mathrm{Im}\,\tau})$ as $\mathrm{Im}\,\tau\to\infty$; and (iii) for every $\tau\in\mathfrak H$ there is $g:\mathbb C\to\mathbb C$ analytic at $\tau$ with $\omega(\mathrm{ofComplex}\,z)=m(\tau)/(z-\tau)+g(z)$ for $z$ in a punctured neighbourhood of $\tau$, where $m(\tau)=e_\tau\cdot D_*(c)(P_\tau)\in\mathbb Z$, and moreover $\omega(\tau)=g(\tau)$ whenever $m(\tau)=0$.
--
--   This is the existence of a differential of the third kind with prescribed integral residues summing to zero, specialised to $X_0(N)$ and transcribed on the upper half plane as a weight-two $\Gamma_0(N)$-invariant function with exponential decay at every cusp. It is used in the construction of meromorphic functions with prescribed divisors and in the Abel–Jacobi statements [`ModularCurve.ComplexPlaceDictionary.exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLattice`](thm.html#ModularCurve.ComplexPlaceDictionary.exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLattice) and [`ModularCurve.ComplexPlaceDictionary.exists_norm_multiplier_eq_one_and_abelJacobi_add_petersson_mem_periodLattice`](thm.html#ModularCurve.ComplexPlaceDictionary.exists_norm_multiplier_eq_one_and_abelJacobi_add_petersson_mem_periodLattice).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionary_exists_slashInvariant_residue_eq_of_degree_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups Topology ModularForm

theorem ModularCurve.ComplexPlaceDictionary.exists_slashInvariant_residue_eq_of_degree_eq_zero
    {N : ℕ} [NeZero N] (D : ModularCurve.ComplexPlaceDictionary N) (c : UpperHalfPlane →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0) :
    ∃ ω : ℍ → ℂ,
      (∀ γ ∈ CongruenceSubgroup.Gamma0 N, ω ∣[(2 : ℤ)] γ = ω) ∧
      (∀ σ : SL(2, ℤ), ∃ δ : ℝ, 0 < δ ∧
        (ω ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im)) ∧
      ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        (∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) =
          (((D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ) : ℤ) : ℂ) / (z - τ) + g z) ∧
        ((D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ) = 0 → ω τ = g τ) := by sorry
