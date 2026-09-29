-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_finite_crossings
-- name    : ModularCurve.XHDRModelAtP.finite_crossings
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/57036396-3bfb-5505-80af-014033bad707
-- title:
--   Finiteness of the crossings of the special fibre at A
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$, let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$, and assume the $q$-expansion $j(q) = q^{-1}\cdot(\text{integral power series } \mathtt{jNum})$ lies in the intermediate field $\mathbb{Q}(\,\text{ratios of integral forms for } \mathrm{SL}_2(\mathbb{Z})\,) \subseteq \mathbb{Q}((q))$; fix a bundle $\mathfrak{X} :$ `XHDRModelAtP p M H hpM hj`, i.e. a Deligne–Rapoport-type integral model datum for the level-$\Gamma_H(M)$ modular curve over the base ring `R p`, comprising the properness, flatness, integrality, normality and relative smoothness properties of the two-chart models at levels $\Gamma_H(M)$ and $\Gamma_{H'}(M/p)$ together with a curve model `Meta` of the geometric function field, an isomorphism `eeta` onto the base change to $\overline{\mathbb{Q}}$ compatible with the Galois action on places, and the remaining fields of the structure. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$, in the sense that the image of $p$ in $\overline{\mathbb{Q}}$ is a non-unit of $A$, whose residue field is of characteristic $p$ and algebraically closed, and let $\rho \colon$ `R p` $\to A$ be a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map of `R p`. Then the underlying type of the scheme-theoretic fibre product of the two morphisms $\mathfrak{X}.\mathrm{comp}\,A\,h_A\,\rho\,h_\rho\,0$ and $\mathfrak{X}.\mathrm{comp}\,A\,h_A\,\rho\,h_\rho\,1$ attached to the model at $A$ is finite.
--
--   This is the finiteness of the crossing locus of the geometric special fibre at $p$ of the Deligne–Rapoport model of $X_H(M)$: the two components indexed by $0$ and $1$ meet in finitely many points, the supersingular points. It is used in the analysis of the local structure of the model at a crossing, notably in the statements identifying the branch ideals at a node and characterising which points specialise to a given crossing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_finite_crossings.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.finite_crossings

    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    Finite ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)) := by sorry
