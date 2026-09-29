-- Prove2me | Theorems.Thm_ModularCurve_CupPairing_exists_isParabolicHom_eq_sub_of_forall_finsum_eq_zero
-- name    : ModularCurve.CupPairing.exists_isParabolicHom_eq_sub_of_forall_finsum_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/1fad4f02-ca44-55c7-81f9-5d46a9403017
-- title:
--   Harmonic functions on SL₂(ℤ)/Γ as coboundaries of parabolic characters
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb Z)$ of finite index containing $-1$, and let $S$ and $T$ denote the usual generators `ModularGroup.S` and `ModularGroup.T`, acting on the coset space $\mathrm{SL}_2(\mathbb Z)/\Gamma$ by left translation. Let $f\colon \mathrm{SL}_2(\mathbb Z)/\Gamma\to\mathbb Z$ be a function such that for every $e\colon\mathrm{SL}_2(\mathbb Z)/\Gamma\to\mathbb Z$ with $e(T\cdot q)=e(q)$ for all $q$, the finite sum $\sum_{q} f(q)\,\bigl(e(q)-e(S\cdot q)\bigr)$ over the coset space vanishes. The assertion is that there is an additive homomorphism $\varphi$ from $\Gamma$, written additively as `Additive Γ`, to $\mathbb Z$ which is parabolic in the sense of [`ModularCurve.Period.IsParabolicHom`](def/ModularCurve_PeriodMap.html#L15), namely $\varphi(\gamma)=0$ for every $\gamma\in\Gamma$ whose matrix has $(\operatorname{tr}\gamma)^2=4$, together with two functions $a,b\colon\mathrm{SL}_2(\mathbb Z)\to\mathbb Z$ satisfying $a(Sg)=a(g)$ and $b(STg)=b(g)$ for all $g$, satisfying $a(g\gamma)=a(g)+\varphi(\gamma)$ and $b(g\gamma)=b(g)+\varphi(\gamma)$ for all $g\in\mathrm{SL}_2(\mathbb Z)$ and $\gamma\in\Gamma$, and such that $f(g\Gamma)=b(g)-a(g)$ for every $g$.
--
--   In the language of Serre's tree for $\mathrm{SL}_2(\mathbb Z)=\mathbb Z/4*_{\mathbb Z/2}\mathbb Z/6$, integer functions on $\mathrm{SL}_2(\mathbb Z)/\Gamma$ are the $1$-cochains of the quotient graph, the hypothesis on $f$ is the vanishing of its sums over the $T$-orbits (the cusps), and the conclusion exhibits $f$ as the coboundary of a pair of vertex potentials whose $\Gamma$-defect is a parabolic character; this is the comparison underlying Manin's description of parabolic cohomology by modular symbols. It is used in the construction of the cup pairing on modular curves, in [`ModularCurve.CupPairing.exists_perfectPairing_intCast_eq_pair`](thm.html#ModularCurve.CupPairing.exists_perfectPairing_intCast_eq_pair).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CupPairing_exists_isParabolicHom_eq_sub_of_forall_finsum_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.CupPairing.exists_isParabolicHom_eq_sub_of_forall_finsum_eq_zero
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (f : SL(2, ℤ) ⧸ Γ → ℤ)
    (hf : ∀ e : SL(2, ℤ) ⧸ Γ → ℤ, (∀ q, e (ModularGroup.T • q) = e q) →
      ∑ᶠ q, f q * (e q - e (ModularGroup.S • q)) = 0) :
    ∃ φ : Additive Γ →+ ℤ, ModularCurve.Period.IsParabolicHom Γ φ ∧
      ∃ a b : SL(2, ℤ) → ℤ, (∀ g, a (ModularGroup.S * g) = a g) ∧
        (∀ g, b (ModularGroup.S * ModularGroup.T * g) = b g) ∧
        (∀ (g : SL(2, ℤ)) (γ : Γ), a (g * γ) = a g + φ (Additive.ofMul γ)) ∧
        (∀ (g : SL(2, ℤ)) (γ : Γ), b (g * γ) = b g + φ (Additive.ofMul γ)) ∧
        ∀ g, f (QuotientGroup.mk g) = b g - a g := by sorry
