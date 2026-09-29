-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_not_isInftySide_of_section_comp_one
-- name    : ModularCurve.XHDRModelAtP.not_isInftySide_of_section_comp_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/9b20c167-0bf2-57c8-a418-c5f3df74cbdc
-- title:
--   Sections closing on component 1 are not ∞-side
-- statement:
--   Fix a prime $p$ and $M\neq 0$ with $p\mid M$ but $p^2\nmid M$, and a subgroup $H\le(\mathbb Z/M)^\times$ containing every unit whose image under the reduction $(\mathbb Z/M)^\times\to(\mathbb Z/(M/p))^\times$ is $1$, with $M/p\neq 0$; assume $j$, in the form of the Laurent series `jqModC ℚ`, lies in the field `qExpFunctionFieldC ℚ ⊤` generated over $\mathbb Q$ by the integral-form ratios for $SL(2,\mathbb Z)$. Let $\mathfrak X$ be a model datum `XHDRModelAtP p M H hpM hj` for the two-chart integral model `toBase p (ΓM M H) hj` over $R_p=\mathbb Z_{(p)}$, whose curve model $\mathfrak X.\mathrm{Meta}$ presents the geometric function field `xHFunctionFieldBar M H` over $\overline{\mathbb Q}$ through the isomorphism $\mathfrak X.\mathrm{eeta}$ onto the base change of the model to $\overline{\mathbb Q}$. Let $A\subset\overline{\mathbb Q}$ be a valuation subring with $p$ a non-unit of $A$, whose residue field $\kappa$ has characteristic $p$ and is algebraically closed, and let $\rho\colon R_p\to A$ be a ring map inducing the structure map $R_p\to\overline{\mathbb Q}$. Let $y$ be a $\overline{\mathbb Q}$-point of $\mathfrak X.\mathrm{Meta}.C$, i.e. a section of $\mathfrak X.\mathrm{Meta}.\mathrm{toBase}$, let $u\colon \operatorname{Spec}A\to X$ be a morphism over $\operatorname{Spec}\rho$ whose restriction along $\operatorname{Spec}$ of the inclusion $A\hookrightarrow\overline{\mathbb Q}$ is $y$ composed with $\mathfrak X.\mathrm{eeta}$ followed by the first projection, and let $u_\kappa$ be a $\kappa$-point of the fibre of the model over $\operatorname{Spec}$ of the composite $R_p\to A\to\kappa$ (its second projection is the identity) whose first projection is the reduction of $u$. Assume finally that there is a closed point $P_0$ of $(\mathfrak X.\mathrm{Mfib}\,A\,hA\,\rho\,h\rho).C$ whose image under $\mathfrak X.\mathrm{efib}$ followed by $\mathfrak X.\mathrm{comp}\,A\,hA\,\rho\,h\rho\,1$ is the image under $u_\kappa$ of the closed point of $\operatorname{Spec}\kappa$. Then the place $W=\mathfrak X.\mathrm{Meta}.\mathrm{pointEquivPlace}\,y$ of `xHFunctionFieldBar M H` over $\overline{\mathbb Q}$ does not satisfy `JHPlaceSpecialization.IsInftySide`: it is not the case both that $\mathrm{ord}_W(x-a)\le 0$ for every element $x$ of the function field with $q$-expansion $j$ and every $a\in A$, and that there are elements $x,x'$ with $q$-expansions $j$ and $j(q^p)$ respectively together with $\tau\in A$ of residue $1$ such that $x'/x^p$ lies in the valuation ring of $W$ with residue the image of $\tau$.
--
--   This is one half of the statement that, for a section of the Deligne–Rapoport model of $X_H(M)$ over a valuation ring above $p$ with $p\parallel M$, the component of the geometric special fibre containing the reduced point determines which of the two cuspidal orientations the generic place carries: a section whose special point lies on the component indexed by $1$ cannot have $j(q^p)/j^p$ taking a value $\equiv 1$ at its generic place while $j$ takes no $A$-integral value there. It is used, together with the complementary dichotomy, by [`ModularCurve.XHDRModelAtP.cuspOrientationInf_and_cuspOrientationZero_of_jHPlaceSpecialization_of_offDiag`](thm.html#ModularCurve.XHDRModelAtP.cuspOrientationInf_and_cuspOrientationZero_of_jHPlaceSpecialization_of_offDiag).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_not_isInftySide_of_section_comp_one.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.not_isInftySide_of_section_comp_one
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    : ¬ (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) (𝔛.Meta.pointEquivPlace y) := by sorry
