-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_eq_xi_of_specializes_of_maximalIdeal_eq_span
-- name    : ModularCurve.XHDRModelAtP.eq_xi_of_specializes_of_maximalIdeal_eq_span
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/21a2b035-4ae5-5de7-a567-ae140c725fbb
-- title:
--   Branch points ξ_∞,ξ₀ are maximal in the special fibre
-- statement:
--   Fix a prime $p$ and $M\neq 0$ with $p\mid M$ but $p^2\nmid M$, a subgroup $H\leq(\mathbb Z/M)^\times$ containing every unit of $\mathbb Z/M$ whose image in $(\mathbb Z/(M/p))^\times$ is $1$, and assume the Laurent series $j$-expansion `jqModC ℚ` ($q^{-1}$ times the integral numerator series) lies in the intermediate field $\mathbb Q\big(\text{intFormRatiosC}\big)$ attached to the full group. Let $\mathfrak X$ be a bundle `XHDRModelAtP p M H hpM hj` of the Deligne–Rapoport data for the two-chart integral model $X$ of level `ΓM M H` over $\operatorname{Spec}(R p)$ (properness, flatness, integrality, local finite presentation, normality of affine sections, properness and relative smoothness of dimension $1$ at the auxiliary level, a geometric curve model over $\overline{\mathbb Q}$ identified with the base change and pinned by $q$-expansions, and the remaining generic-fibre and special-fibre data). Let $A\subseteq\overline{\mathbb Q}$ be a valuation subring with $p$ a nonunit of $A$, whose residue field is algebraically closed of characteristic $p$, and $\rho\colon R p\to A$ a ring map whose composite with the inclusion $A\hookrightarrow\overline{\mathbb Q}$ is the structure map. Let $O$ be a commutative local ring, $\rho_O\colon R p\to O$, $\varpi\in O$ with $\mathfrak m_O=(\varpi)$, and $\mathrm{to}\kappa\colon O\to\kappa_A$ a ring map with $\mathrm{to}\kappa\circ\rho_O$ equal to $\rho$ followed by the residue map and $\mathrm{to}\kappa(\varpi)=0$. Write $X_O$ for the pullback of $X\to\operatorname{Spec}(R p)$ along $\operatorname{Spec}(\rho_O)$, with projection $X_O\to\operatorname{Spec} O$. Then for the two points $\xi_\infty=\mathfrak X.\xi\mathrm{inf}$ and $\xi_0=\mathfrak X.\xi\mathrm{zero}$ of $X_O$ produced from these data: every $y\in X_O$ lying outside the preimage of the basic open $D(\varpi)\subseteq\operatorname{Spec} O$ and specialising to $\xi_\infty$ (respectively to $\xi_0$) is equal to $\xi_\infty$ (respectively to $\xi_0$).
--
--   The special fibre at $p$ of the Deligne–Rapoport model of $X_H(M)$ with $p\parallel M$ is a union of two branches; the assertion is that the two marked points $\xi_\infty,\xi_0$ of $X_O$ are maximal points of the fibre $\varpi=0$, i.e. no point of that fibre properly generalises them. It is the form of the statement keyed to a uniformiser $\varpi$ of the local ring $O$, and is used in reading stalks of $X_O$ along the two branches.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_eq_xi_of_specializes_of_maximalIdeal_eq_span.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.eq_xi_of_specializes_of_maximalIdeal_eq_span
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsLocalRing O] (ρO : R p →+* O)
    (ϖ : O) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ})
    (toκ : O →+* IsLocalRing.ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ) (hϖκ : toκ ϖ = 0) :
    (∀ y : ↥(XO (ΓM M H) hj ρO), y ∉ (XO.toBase (ΓM M H) hj ρO) ⁻¹ᵁ (PrimeSpectrum.basicOpen ϖ : (Spec (CommRingCat.of O)).Opens) → y ⤳ 𝔛.ξinf A hA ρ hρ ρO toκ htoκ → y = 𝔛.ξinf A hA ρ hρ ρO toκ htoκ) ∧
    (∀ y : ↥(XO (ΓM M H) hj ρO), y ∉ (XO.toBase (ΓM M H) hj ρO) ⁻¹ᵁ (PrimeSpectrum.basicOpen ϖ : (Spec (CommRingCat.of O)).Opens) → y ⤳ 𝔛.ξzero A hA ρ hρ ρO toκ htoκ → y = 𝔛.ξzero A hA ρ hρ ρO toκ htoκ) := by sorry
