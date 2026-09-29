-- Prove2me | Theorems.Thm_ModularCurve_exists_fibreCurveModels_twoChartIntegralModel_qExpFunctionFieldC_isPlaceReductionQExpModL_of_not_dvd
-- name    : ModularCurve.exists_fibreCurveModels_twoChartIntegralModel_qExpFunctionFieldC_isPlaceReductionQExpModL_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/9d1a87ff-1c44-5c7b-8cf4-92a301d6ae65
-- title:
--   Fibres of the two-chart model of X_Γ at p∤ M
-- statement:
--   Let $M\ge 1$, let $\Gamma\le\mathrm{SL}_2(\mathbb Z)$ satisfy $\Gamma_1(M)\le\Gamma\le\Gamma_0(M)$, let $p$ be a prime with $p\nmid M$, and let $j$ be a nonzero element of $F:=$ `qExpFunctionFieldC ℚ Γ`, the subfield of $\mathbb Q((q))$ generated over $\mathbb Q$ by `intFormRatiosC ℚ Γ`, whose underlying Laurent series is `jqModC ℚ` $=q^{-1}\cdot$ (the reduction of `jNum`). Write $Z=$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) for the subring of rationals whose denominator is coprime to $p$, and $X$ for `TwoChartIntegralModel` $Z$ $F$ $j$, the pushout of the two chart maps, with its structure morphism to $\operatorname{Spec} Z$. Then there exist: a `CurveModel` $M_\eta$ over $\overline{\mathbb Q}$ for the field `laurentBaseChange` $\overline{\mathbb Q}$ $F$ (an integral scheme, proper and smooth of relative dimension $1$ over $\overline{\mathbb Q}$, with a ring isomorphism of that field onto its function field over the base, and a bijection from closed points to places matching stalks with valuation subrings); an isomorphism $e_\eta$ from $M_\eta.C$ to $X\times_{\operatorname{Spec}Z}\operatorname{Spec}\overline{\mathbb Q}$ commuting with the maps to $\operatorname{Spec}\overline{\mathbb Q}$; a compatibility stating that for $\sigma\in\mathrm{Aut}(\overline{\mathbb Q}/\mathbb Q)$ and sections $x,x'$ of $M_\eta.C$ over $\overline{\mathbb Q}$ whose images in $X$ satisfy $x'=\mathrm{Spec}(\sigma)$ followed by $x$, one has `pointEquivPlace` $x'=$ `arithmeticGalois` $F\,\sigma\cdot$ `pointEquivPlace` $x$ (the coefficientwise semilinear action on places); ring maps $\rho_A: Z\to A$, for each valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ a nonunit of $A$, whose composition with $A\hookrightarrow\overline{\mathbb Q}$ is the structural map; and `CurveModel`s $M_A$ over the residue field $\kappa_A$ for `qExpFunctionFieldC` $\kappa_A$ $\Gamma$ together with isomorphisms $e_A:M_A.C\to X\times_{\operatorname{Spec}Z}\operatorname{Spec}\kappa_A$ over $\operatorname{Spec}\kappa_A$ (the base change along $\mathrm{residue}\circ\rho_A$) — such that for every such $A$ with $\kappa_A$ algebraically closed there is a map $r$ from places of `laurentBaseChange` $\overline{\mathbb Q}$ $F$ to places of `qExpFunctionFieldC` $\kappa_A$ $\Gamma$ satisfying `IsPlaceReductionQExpModL A Γ r` (the predicate `IsLaurentPlaceReduction` for $A$ and its residue map) and having the following specialisation property: whenever $x_A:\operatorname{Spec}A\to X$ lies over $\operatorname{Spec}(\rho_A)$, $x$ is a $\overline{\mathbb Q}$-section of $M_\eta.C$ and $y$ a $\kappa_A$-section of $M_A.C$ whose images in $X$ are obtained from $x_A$ by $A\hookrightarrow\overline{\mathbb Q}$ and by $A\to\kappa_A$ respectively, then the place attached to $y$ is $r$ applied to the place attached to $x$.
--
--   This is the geometric content of Igusa's Kroneckerian model of $X_\Gamma$ over $\mathbb Z_{(p)}$ for $p\nmid M$: its generic fibre and its fibres over residue fields of valuation rings of $\overline{\mathbb Q}$ above $p$ are smooth proper curve models of the corresponding $q$-expansion function fields, the Galois action on generic points is the coefficientwise action on places, and specialisation of points realises the reduction of places in the sense of Deuring. It is used by [`ModularCurve.exists_abelianSchemePropertyBundle_model_jH`](thm.html#ModularCurve.exists_abelianSchemePropertyBundle_model_jH) to produce the abelian-scheme model of the Jacobian $J_H(M)$ over $\mathbb Z_{(p)}$ with its reduction map on divisor classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_fibreCurveModels_twoChartIntegralModel_qExpFunctionFieldC_isPlaceReductionQExpModL_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra IsLocalRing
open AlgebraicCurve
open ModularCurve

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_fibreCurveModels_twoChartIntegralModel_qExpFunctionFieldC_isPlaceReductionQExpModL_of_not_dvd
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (j : ↥(qExpFunctionFieldC ℚ Γ)) [Fact (j ≠ 0)] (hj : (j : LaurentSeries ℚ) = jqModC ℚ) :
    ∃ (Mη : CurveModel (AlgebraicClosure ℚ)
        ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)))
      (eη : Mη.C ⟶ pullback
        (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
        (Spec.map (CommRingCat.ofHom
          (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))))
      (_ : IsIso eη)
      (_ : eη ≫ pullback.snd _ _ = Mη.toBase)
      (_ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
        x'.1 ≫ eη ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
            x.1 ≫ eη ≫ pullback.fst _ _ →
        Mη.pointEquivPlace x' =
          arithmeticGalois (L := AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ) σ •
            Mη.pointEquivPlace x)
      (ρ : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        (↥(GaloisRep.ratLocalizedAt p) →+* ↥A))
      (_ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
        A.subtype.comp (ρ A hA) = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
      (Ms : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        CurveModel (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))
      (es : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
        (Ms A hA).C ⟶ pullback
          (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
          (Spec.map (CommRingCat.ofHom ((residue ↥A).comp (ρ A hA)))))
      (_ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p), IsIso (es A hA))
      (_ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
        es A hA ≫ pullback.snd _ _ = (Ms A hA).toBase),
    ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [IsAlgClosed (ResidueField ↥A)],
      ∃ r : Place (AlgebraicClosure ℚ)
            ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) →
          Place (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ),
        IsPlaceReductionQExpModL A Γ r ∧
        ∀ (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ A hA)))
            (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j))
          (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
          (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C //
            q ≫ (Ms A hA).toBase = 𝟙 _}),
          x.1 ≫ eη ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1 →
          y.1 ≫ es A hA ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xA.1 →
          (Ms A hA).pointEquivPlace y = r (Mη.pointEquivPlace x) := by sorry
