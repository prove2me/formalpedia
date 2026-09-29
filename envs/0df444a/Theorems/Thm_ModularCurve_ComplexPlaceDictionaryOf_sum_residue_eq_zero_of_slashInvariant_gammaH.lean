-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_sum_residue_eq_zero_of_slashInvariant_gammaH
-- name    : ModularCurve.ComplexPlaceDictionaryOf.sum_residue_eq_zero_of_slashInvariant_gammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/6cbba976-f125-50b9-b1c2-bff33a3e49a8
-- title:
--   Residue theorem for weight-two forms on X_H(M)
-- statement:
--   Let $M\ge 1$ and let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$, and write $\Gamma_H(M)$ for the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$ consisting of those matrices in $\Gamma_0(M)$ whose lower-right entry reduces mod $M$ into $H$. Let $F$ be the $q$-expansion function field [`ModularCurve.xHFunctionField M H`](def/ModularCurve_XH.html#L79), an intermediate field of $\mathbb{Q}((q))$ attached to $\Gamma_H(M)$, and let [`ModularCurve.laurentBaseChange ℂ F`](def/ModularCurve_LaurentCoeff.html#L103) be the intermediate field of $\mathbb{C}((q))$ generated over $\mathbb{C}$ by the coefficientwise image of $F$; its places in the sense of [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22) are the proper valuation subrings containing $\mathbb{C}$ that are principal ideal rings. Let $D$ be a complex place dictionary for $(\Gamma_H(M), F)$, that is, a map $\tau\mapsto D.\mathrm{pt}(\tau)$ from the upper half-plane to these places together with positive integers $D.\mathrm{ramification}(\tau)$, invariant under $\Gamma_H(M)$ and compatible with boundedness and meromorphic orders of the functions realising elements of the field on $\mathfrak{H}$. Let $\omega:\mathfrak{H}\to\mathbb{C}$ and let $r$ be a finitely supported $\mathbb{C}$-valued function on the places. Assume: $\omega\mid_2\gamma=\omega$ for all $\gamma\in\Gamma_H(M)$; for every $\sigma\in\mathrm{SL}_2(\mathbb{Z})$ there is $\delta>0$ with $\omega\mid_2\sigma = O(e^{-\delta\,\mathrm{Im}\,\tau})$ as $\mathrm{Im}\,\tau\to\infty$; every place in the support of $r$ is of the form $D.\mathrm{pt}(\tau)$; and for every $\tau\in\mathfrak{H}$ there is $g$ analytic at $\tau$ with $\omega(z) = D.\mathrm{ramification}(\tau)\,r(D.\mathrm{pt}(\tau))/(z-\tau) + g(z)$ on a punctured neighbourhood of $\tau$. Then $\sum_P r(P)=0$.
--
--   This is the residue theorem for the meromorphic differential on the modular curve $X_H(M)$ whose pull-back to the upper half-plane is $\omega(\tau)\,d\tau$, stated on the universal cover in terms of a complex place dictionary: the residues of a $\Gamma_H(M)$-invariant weight-two form with exponential decay at all cusps and at worst simple poles sum to zero. It is used in the construction of a weight-two form with prescribed residues attached to a degree-zero divisor on $X_H(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionaryOf_sum_residue_eq_zero_of_slashInvariant_gammaH.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_XH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology ModularForm

theorem ModularCurve.ComplexPlaceDictionaryOf.sum_residue_eq_zero_of_slashInvariant_gammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (ω : ℍ → ℂ) (r : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)) →₀ ℂ)
    (hΓ : ∀ γ ∈ CohCarrier.GammaH M H, ω ∣[(2 : ℤ)] γ = ω)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ δ : ℝ, 0 < δ ∧
        (ω ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im))
    (hsupp : ∀ P ∈ r.support, ∃ τ : ℍ, D.pt τ = P)
    (hloc : ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) =
          (D.ramification τ : ℂ) * r (D.pt τ) / (z - τ) + g z) :
    r.sum (fun _ a => a) = 0 := by sorry
