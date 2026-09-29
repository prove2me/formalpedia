-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_isRational_comp_eq_pointEquivPlace_and_eq_of_comp_eq
-- name    : ModularCurve.XHDRModelAtP.exists_isRational_comp_eq_pointEquivPlace_and_eq_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/670e98f4-e778-59bb-8db3-b5d00d4d1842
-- title:
--   Sections over A and rational places of X_H
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$, $p^{2} \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^{\times}$ containing every unit whose image under $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/(M/p))^{\times}$ is $1$; assume `jqModC ℚ` lies in `qExpFunctionFieldC ℚ ⊤`, and let $\mathfrak{X}$ be an `XHDRModelAtP p M H hpM hj` package, which in particular provides a curve model $\mathfrak{X}.\mathrm{Meta}$ of `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$ and an isomorphism $\mathfrak{X}.\mathrm{eeta}$ of its underlying scheme with $X_{\overline{\mathbb{Q}}} :=$ the base change of `toBase p (ΓM M H) hj` along $R_p \to \overline{\mathbb{Q}}$. Further data: a valuation subring $A$ of $\overline{\mathbb{Q}}$ in which $p$ is a non-unit, with algebraically closed residue field of characteristic $p$, and $\rho : R_p \to A$ lifting the structure map; a discrete valuation domain $O$ with maximal ideal $(p)$, maps $\rho_O : R_p \to O$, $\mathrm{to}\kappa : O \to \kappa(A)$, $j_O : O \to \overline{\mathbb{Q}}$ and $\iota_A : O \to A$ making the evident triangles commute; a point $n$ of the fibre product of $\mathfrak{X}.\mathrm{comp}\,A\,hA\,\rho\,h\rho\,0$ and $\mathfrak{X}.\mathrm{comp}\,A\,hA\,\rho\,h\rho\,1$, with image $x$ in `XO (ΓM M H) hj ρO` under the first projection followed by the component $0$ map and `bcMap`; an $e \ge 1$, an open $U \subseteq X_O$ containing $x$, and a morphism $f$ from $U$ to $\operatorname{Spec} O[X_0,X_1]/(X_0X_1 - p^{e})$ over $\operatorname{Spec} O$, subject to the node conditions at $x$ (the point of the crossing locus has fibre exactly $x$; at points over $x$ the stalk map is flat, carries the maximal ideal onto the maximal ideal and induces an isomorphism of residue fields, and $f$ is étale on a neighbourhood; the two coordinate axes correspond to the images of the two components), summarised here. Then, with $\mathrm{pr}_J : X_{\overline{\mathbb{Q}}} \to X_O$ the map induced by the identity and $\operatorname{Spec} j_O$: (i) for every $s : \operatorname{Spec} A \to U$ with $s$ followed by $U \hookrightarrow X_O$ and the structure map equal to $\operatorname{Spec} \iota_A$, there is a place $W$ of `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$ (a proper valuation subring containing $\overline{\mathbb{Q}}$ whose maximal ideal is principal) which is rational, i.e. $\overline{\mathbb{Q}}$ surjects onto its residue field, such that $\operatorname{Spec} A.\mathrm{subtype}$ followed by $s$ and $U \hookrightarrow X_O$ equals the $\overline{\mathbb{Q}}$-point $\mathfrak{X}.\mathrm{Meta}.\mathrm{pointEquivPlace}^{-1}(W)$ followed by $\mathfrak{X}.\mathrm{eeta}$ and $\mathrm{pr}_J$; and (ii) the assignment $W \mapsto \mathrm{pointEquivPlace}^{-1}(W)$ followed by $\mathfrak{X}.\mathrm{eeta}$ and $\mathrm{pr}_J$ is injective.
--
--   This is the dictionary, in the node-annulus setting, between $A$-valued sections of the integral model over $O$ and rational places of the geometric function field of $X_H(M)$: the generic fibre of such a section is a $\overline{\mathbb{Q}}$-point of the base change, hence, through the comparison isomorphism with the curve model, a place, and distinct places give distinct points. It is used in the subsequent statements producing an annulus parameter at a node and computing orders and chart readings along the two components.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_isRational_comp_eq_pointEquivPlace_and_eq_of_comp_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
  ModularCurve.JZeroNeronObjectAtP MvPolynomial
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_isRational_comp_eq_pointEquivPlace_and_eq_of_comp_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (toκ : O →+* ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)

    (jO : O →+* AlgebraicClosure ℚ) (hjO : jO.comp ρO = algebraMap (R p) (AlgebraicClosure ℚ))
    (ιA : O →+* ↥A) (hιA : A.subtype.comp ιA = jO) (hιAκ : (IsLocalRing.residue ↥A).comp ιA = toκ)

    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (e : ℕ) (he : 1 ≤ e) (U : (XO (ΓM M H) hj ρO).Opens) (hxU : (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n ∈ U)
    (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e))
    (hover : f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e)))) = U.ι ≫ pullback.snd _ _)
    (hfib : ∀ y : ↥(U : Scheme.{0}),
      (CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal ∧ CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ↔ U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n)
    (hpt : ∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n →
      (f.stalkMap y).hom.Flat ∧ Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧ IsIso (f.residueFieldMap y))
    (het : ∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n → ∃ V : (U : Scheme.{0}).Opens, y ∈ V ∧ Etale (V.ι ≫ f))
    (hor₁ : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal → U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base)
    (hor₂ : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal → U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base)
    (hor₃ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base → CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal)
    (hor₄ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base → CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prJ : XQ ⟶ XO (ΓM M H) hj ρO :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO])
    (∀ s : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0}),
      s ≫ U.ι ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA) →
      ∃ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), W.IsRational ∧
        barPt A ≫ s ≫ U.ι = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prJ) ∧
    (∀ W W' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prJ = ((𝔛.Meta).pointEquivPlace.symm W').1 ≫ 𝔛.eeta ≫ prJ → W = W') := by sorry
