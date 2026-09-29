-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionary_exists_slashInvariant_residue_ne_zero_of_pt_ne
-- name    : ModularCurve.ComplexPlaceDictionary.exists_slashInvariant_residue_ne_zero_of_pt_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/f4f2bf9b-a13b-54bd-a017-a4dd96cbcc9d
-- title:
--   Third-kind differential on X₀(N) with two prescribed poles
-- statement:
--   Let $N\ge 1$ and let $F_N=$ `laurentBaseChange ℂ (modularFunctionFieldFull N)`, the subfield of $\mathbb C((q))$ generated over $\mathbb C$ by the coefficientwise images of the $q$-expansions $j(q^d)$ for the nonzero divisors $d\mid N$. Let $D$ be a complex place dictionary of level $N$: a map $\tau\mapsto P_\tau$ from $\mathfrak H$ to the places of $F_N/\mathbb C$ (valuation subrings containing $\mathbb C$, proper and principal) together with integers $e_\tau=D.\mathrm{ramification}\,\tau\ge 1$, invariant under $\Gamma_0(N)$, such that $x\in F_N$ lies in the valuation subring of $P_\tau$ exactly when $\|\mathrm{realize}\,N\,x\|$ is bounded near $\tau$ on $\mathfrak H\setminus\{\tau\}$, and such that for $x\ne0$ the meromorphic order of $z\mapsto \mathrm{realize}\,N\,x\,(\mathrm{ofComplex}\,z)$ at $\tau$ is $e_\tau\cdot\operatorname{ord}_{P_\tau}(x)$. Assume $\tau_1,\tau_2\in\mathfrak H$ satisfy $P_{\tau_1}\ne P_{\tau_2}$. Then there exist $\omega:\mathfrak H\to\mathbb C$ and a finitely supported $r$ from the places of $F_N/\mathbb C$ to $\mathbb C$ with: $\omega\mid_2\gamma=\omega$ for all $\gamma\in\Gamma_0(N)$; for each $\sigma\in\mathrm{SL}_2(\mathbb Z)$ some $\delta>0$ with $\omega\mid_2\sigma=O(e^{-\delta\operatorname{Im}\tau})$ at $\operatorname{Im}\to\infty$; $r(P_{\tau_1})\ne0$; $r(P)\ne0$ only for $P\in\{P_{\tau_1},P_{\tau_2}\}$; and for every $\tau\in\mathfrak H$ a function $g$ analytic at $\tau$ with $\omega(\mathrm{ofComplex}\,z)=e_\tau\,r(P_\tau)/(z-\tau)+g(z)$ for all $z\ne\tau$ near $\tau$.
--
--   This is the Riemann–Roch existence of a differential of the third kind on $X_0(N)$ with polar divisor supported in two prescribed distinct points, transcribed through the place dictionary into a $\Gamma_0(N)$-invariant weight-two function on the upper half plane that is exponentially small at every cusp and has at most simple poles, with nonzero residue at $\tau_1$. It is used by [`ModularCurve.ComplexPlaceDictionary.exists_slashInvariant_residue_eq_of_degree_eq_zero`](thm.html#ModularCurve.ComplexPlaceDictionary.exists_slashInvariant_residue_eq_of_degree_eq_zero), where residues at the two points are matched.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionary_exists_slashInvariant_residue_ne_zero_of_pt_ne.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups Topology ModularForm

theorem ModularCurve.ComplexPlaceDictionary.exists_slashInvariant_residue_ne_zero_of_pt_ne
    {N : ℕ} [NeZero N] (D : ModularCurve.ComplexPlaceDictionary N) {τ₁ τ₂ : ℍ}
    (hne : D.pt τ₁ ≠ D.pt τ₂) :
    ∃ (ω : ℍ → ℂ) (r : AlgebraicCurve.Place ℂ
        (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) →₀ ℂ),
      (∀ γ ∈ CongruenceSubgroup.Gamma0 N, ω ∣[(2 : ℤ)] γ = ω) ∧
      (∀ σ : SL(2, ℤ), ∃ δ : ℝ, 0 < δ ∧
        (ω ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im)) ∧
      r (D.pt τ₁) ≠ 0 ∧
      (∀ P, r P ≠ 0 → P = D.pt τ₁ ∨ P = D.pt τ₂) ∧
      ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) =
          (D.ramification τ : ℂ) * r (D.pt τ) / (z - τ) + g z := by sorry
