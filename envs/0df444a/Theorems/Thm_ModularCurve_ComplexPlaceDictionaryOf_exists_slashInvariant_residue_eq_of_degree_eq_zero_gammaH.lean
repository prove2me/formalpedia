-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_slashInvariant_residue_eq_of_degree_eq_zero_gammaH
-- name    : ModularCurve.ComplexPlaceDictionaryOf.exists_slashInvariant_residue_eq_of_degree_eq_zero_gammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/11784cde-c088-5a73-af4c-bba5455f378a
-- title:
--   Weight-two forms with prescribed residue divisor on X_H(M)
-- statement:
--   Let $M\ge 1$ be a natural number and $H$ a subgroup of $(\mathbb{Z}/M)^\times$, and write $\Gamma_H(M)$ for the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $SL(2,\mathbb{Z})$, namely the image in $SL(2,\mathbb{Z})$ of the set of $\gamma\in\Gamma_0(M)$ whose lower-right entry reduces into $H$. Let $D$ be a complex place dictionary for $\Gamma_H(M)$ and the $q$-expansion function field $F=$ [`ModularCurve.xHFunctionField M H`](def/ModularCurve_XH.html#L79), i.e. a map $\mathrm{pt}:\mathfrak H\to\{$places of the $\mathbb{C}$-base change $\mathbb{C}F$ of $F\}$ together with a positive integer $e_\tau=$ `D.ramification` $\tau$, such that $\mathrm{pt}$ is constant on $\Gamma_H(M)$-orbits, $x$ lies in the valuation ring of $\mathrm{pt}(\tau)$ exactly when the realisation of $x$ as a function on $\mathfrak H$ is bounded near $\tau$, and the meromorphic order at $\tau$ of that realisation equals $e_\tau\cdot\mathrm{ord}_{\mathrm{pt}(\tau)}(x)$ for $x\ne 0$. Let $c:\mathfrak H\to\mathbb{Z}$ be finitely supported and let $\tilde c=\sum_\tau c(\tau)\,\mathrm{pt}(\tau)$ be its push-forward divisor on $\mathbb{C}F$, assumed of degree $0$, the degree being $\sum_P \tilde c(P)\deg P$. Then there exists $\omega:\mathfrak H\to\mathbb{C}$ with: $\omega\mid_2\gamma=\omega$ for every $\gamma\in\Gamma_H(M)$; for each $\sigma\in SL(2,\mathbb{Z})$ some $\delta>0$ with $\omega\mid_2\sigma=O(e^{-\delta\,\mathrm{Im}\,\tau})$ as $\mathrm{Im}\,\tau\to\infty$; and for each $\tau\in\mathfrak H$ a function $g$ analytic at $\tau\in\mathbb{C}$ such that $\omega(z)=m(\tau)/(z-\tau)+g(z)$ for $z$ in a punctured neighbourhood of $\tau$, where $m(\tau)=e_\tau\,\tilde c(\mathrm{pt}(\tau))\in\mathbb{Z}$ is cast into $\mathbb{C}$, and moreover $\omega(\tau)=g(\tau)$ whenever $m(\tau)=0$.
--
--   This is the existence of a differential of the third kind on $X_H(M)$ with prescribed residue divisor, pulled back to the upper half-plane as a weight-two invariant function with simple poles of residue $\tilde c(P)$ and exponential decay at every cusp. It is the input to the Abel–Jacobi statements for $X_H(M)$, and is obtained from the two-pole case together with the vanishing of the sum of residues of such a form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_slashInvariant_residue_eq_of_degree_eq_zero_gammaH.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_XH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups Topology ModularForm

theorem ModularCurve.ComplexPlaceDictionaryOf.exists_slashInvariant_residue_eq_of_degree_eq_zero_gammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (c : UpperHalfPlane →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0) :
    ∃ ω : UpperHalfPlane → ℂ,
      (∀ γ ∈ CohCarrier.GammaH M H, ω ∣[(2 : ℤ)] γ = ω) ∧
      (∀ σ : SL(2, ℤ), ∃ δ : ℝ, 0 < δ ∧
        (ω ∣[(2 : ℤ)] σ) =O[UpperHalfPlane.atImInfty] fun τ : UpperHalfPlane => Real.exp (-δ * τ.im)) ∧
      ∀ τ : UpperHalfPlane, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        (∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (UpperHalfPlane.ofComplex z) =
          (((D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ) : ℤ) : ℂ) / (z - τ) + g z) ∧
        ((D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ) = 0 → ω τ = g τ) := by sorry
