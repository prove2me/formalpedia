-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_isInftySide_of_isCuspidal_of_section_comp_zero
-- name    : ModularCurve.XHDRModelAtP.isInftySide_of_isCuspidal_of_section_comp_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/4025750e-8ea6-55ed-ac3a-eae3e1ec5bae
-- title:
--   Cuspidal place specialising into component 0 is ∞-side
-- statement:
--   Fix a prime $p$ and a nonzero modulus $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image in $(\mathbb{Z}/(M/p))^\times$ is $1$, with $M/p$ nonzero, and assume the $q$-expansion `jqModC ℚ` lies in the intermediate field `qExpFunctionFieldC ℚ ⊤`. Let $\mathfrak{X}$ be an integral model datum `XHDRModelAtP p M H hpM hj` for level $\Gamma_M(M,H)$ over `R p`, with its curve model $\mathfrak{X}.\mathrm{Meta}$ over $\overline{\mathbb{Q}}$ with function field `xHFunctionFieldBar M H` and its isomorphism $\mathfrak{X}.\eta$ onto the geometric generic fibre. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho : \mathrm{R}\,p \to A$ be a ring homomorphism compatible with the structural map to $\overline{\mathbb{Q}}$. Let $y$ be a $\overline{\mathbb{Q}}$-point of $\mathfrak{X}.\mathrm{Meta}.C$ over $\mathrm{Spec}\,\overline{\mathbb{Q}}$, and $u$ a morphism $\mathrm{Spec}\,A \to X$ over $\mathrm{Spec}(\mathrm{R}\,p)$ along $\rho$ whose restriction to $\mathrm{Spec}\,\overline{\mathbb{Q}}$ equals $y$ followed by $\mathfrak{X}.\eta$ and the first projection. Let $u_\kappa$ be a section of the fibre of the model at $\mathrm{residue}\circ\rho$ (its second projection is the identity) whose first projection is the reduction of $u$, and let $P_0$ be a closed point of $(\mathfrak{X}.\mathrm{Mfib}\,A\,hA\,\rho\,h\rho).C$ mapping, under $\mathfrak{X}.\mathrm{efib}$ followed by $\mathfrak{X}.\mathrm{comp}\,A\,hA\,\rho\,h\rho\,0$, to the image of the closed point of $\kappa$ under $u_\kappa$. Assume the place $W$ of `xHFunctionFieldBar M H` attached to $y$ by $\mathfrak{X}.\mathrm{Meta}.\mathrm{pointEquivPlace}$ is cuspidal, i.e. for every element $x$ of the function field whose Laurent expansion is `jqModC` and every $a \in A$ one has $\mathrm{ord}_W(x - a) \le 0$. Then $W$ is on the $\infty$-side: it is cuspidal, and there are elements $x, x'$ of the function field with expansions `jqModC` and `qExpand p (jqModC)` respectively, and $\tau \in A$ of residue $1$, such that $x'/x^p$ lies in the valuation ring of $W$ with residue the image of $\tau$.
--
--   This is the component-wise orientation of cusps on the Deligne–Rapoport model of $X_H(M)$ at a prime $p$ exactly dividing $M$: a section of the model through a cuspidal geometric point whose reduction lands on the component indexed $0$ of the special fibre forces the normalised ratio $j(q^p)/j^p$ to take a value congruent to $1$ at the corresponding place. It feeds the cusp-orientation and local-semicontinuity statements used to separate the two copies of $X_{H'}(M/p)_\kappa$ in the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_isInftySide_of_isCuspidal_of_section_comp_zero.lean

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

theorem ModularCurve.XHDRModelAtP.isInftySide_of_isCuspidal_of_section_comp_zero
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
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (hc : (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A)) (𝔛.Meta.pointEquivPlace y)) :
    (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) (𝔛.Meta.pointEquivPlace y) := by sorry
