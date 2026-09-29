-- Prove2me | Theorems.Thm_ModularCurve_exists_pts_relJacobian_jZero_of_representsRelSubPic_of_ratCurveModel
-- name    : ModularCurve.exists_pts_relJacobian_jZero_of_representsRelSubPic_of_ratCurveModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/2c38fe3d-8e14-5f3d-bb29-23d34b448bc3
-- title:
--   Points, reduction and Hecke action on a representing relative Jacobian
-- statement:
--   Fix $p\ge 1$ and a prime $\ell$ with $\ell\nmid p$, and write $R=\mathbb{Z}_{(\ell)}$ for [`GaloisRep.ratLocalizedAt`](def/GaloisRep_Flat.html#L8) $\ell$, the subring of rationals whose denominator is coprime to $\ell$. Let $c\colon X\to\operatorname{Spec}R$ be proper, smooth of relative dimension $1$ and geometrically integral, with a section $\varepsilon$. Assume given: a curve model $M_\eta$ over $\overline{\mathbb{Q}}$ of `modularFunctionFieldBar p` (the $\overline{\mathbb{Q}}$-base change inside Laurent series of the field generated over $\mathbb{Q}$ by the $q$-expansions $\mathrm{qExpand}\,d\,j_q$ for $d\mid p$) together with an isomorphism $e_\eta$ of $M_\eta.C$ with the $\overline{\mathbb{Q}}$-base change of $c$ commuting with the structure maps, and the compatibility `hgal` that transporting a $\overline{\mathbb{Q}}$-point along $\operatorname{Spec}g$, $g\in\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, corresponds on places to the action of the semilinear automorphism `arithmeticGalois`$(g)$; for each valuation subring $A\subset\overline{\mathbb{Q}}$ with $\ell\in A$ non-unit, a ring map $\rho_A\colon R\to A$ lifting $R\to\overline{\mathbb{Q}}$, a curve model $M_A$ over the residue field $\kappa_A$ of `modularFunctionFieldFullC` $\kappa_A\,p$ isomorphic over the base to the $\kappa_A$-fibre of $c$, and (for $\kappa_A$ algebraically closed) a map $r$ of places satisfying `IsPlaceReductionModL` under which the place of the reduction of any $A$-point of $X$ is $r$ of the place of its generic point; a curve model $M_0$ over $\mathbb{Q}$ of `modularFunctionFieldFull p` isomorphic over the base to the $\mathbb{Q}$-fibre of $c$, with the compatibility `hcompat` identifying, for matching points, the valuation subring of the place of $x$ pulled back along $\overline{\mathbb{Q}}\otimes_{\mathbb{Q}}$-inclusion of the right factor followed by `baseChangeEquiv` with that of $M_0$'s place at the corresponding closed point; and finally a pointed $R$-scheme datum $D$ (a scheme with structure map $D.\mathrm{toBase}$ and a zero section) with a witness $h_D$ that $D$ represents the subfunctor of the $\varepsilon$-rigidified relative Picard presheaf of $c$ cut out by fibrewise algebraic equivalence to zero, $D.\mathrm{toBase}$ being smooth, proper and geometrically connected. Then, for the Hecke-module structure `heckeModuleBar p` on $J_0(p)=\mathrm{Pic}^0(\overline{\mathbb{Q}},$ `modularFunctionFieldBar p`$)$, there exist a bijection $\mathrm{pts}$ from $J_0(p)$ to the $\overline{\mathbb{Q}}$-points of $D$ over $R$ and a family $\varphi\colon$ `HeckeAlg` $\to$ endomorphisms of $D$ over $D.\mathrm{toBase}$ such that: $D.\mathrm{toBase}$ is smooth, proper, has connected fibres and admits a relative group law; the relative group law supplied by $h_D$ is commutative on $T$-points; $\mathrm{pts}$ is additive for it; $\mathrm{pts}(\sigma\cdot x)=\operatorname{Spec}\sigma$ followed by $\mathrm{pts}(x)$ for $\sigma\in\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$; for every $A$ over $\ell$ there are $\sigma_A\colon\operatorname{Spec}A\to\operatorname{Spec}R$ and bijections $\mathrm{pts}_A$ from $J_0(p)$ to $A$-points and $\mathrm{pts}_{\mathrm{sp}}$ from $\mathrm{Pic}^0(\kappa_A,$ `modularFunctionFieldFullC` $\kappa_A\,p)$ to $\kappa_A$-points of $D$ over $\sigma_A$, with $\mathrm{pts}_A(x)$ the same morphism as $\mathrm{pts}(x)$, $\mathrm{pts}_{\mathrm{sp}}$ additive, and, whenever `ReductionInputsModL A p` holds, each $x$ extending to an $A$-point of $D$ whose generic fibre is $\mathrm{pts}_A(x)$ and whose reduction is $\mathrm{pts}_{\mathrm{sp}}$ of the reduction of $x$; and each $\varphi(t)$ is a homomorphism for the relative group law on $T$-points with $\mathrm{pts}(t\cdot x)=\mathrm{pts}(x)$ followed by $\varphi(t)$.
--
--   This is the construction of the relative Jacobian $J_0(p)$ over $\mathbb{Z}_{(\ell)}$ on a scheme already known to represent the $\mathrm{Pic}^0$-cut of the rigidified relative Picard functor: it records the abelian-scheme properties, the Galois-equivariant parametrisation of the generic points by the divisor class group of the modular function field, the Deuring-compatible specialisation of points modulo $\ell$, and the Hecke endomorphisms. It is the form of the statement used by [`ModularCurve.exists_relJacobian_jZero_of_smoothProperModel_of_finiteMapData_of_ratCurveModel`](thm.html#ModularCurve.exists_relJacobian_jZero_of_smoothProperModel_of_finiteMapData_of_ratCurveModel), where the representing scheme is produced from chart data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_pts_relJacobian_jZero_of_representsRelSubPic_of_ratCurveModel.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicCurve IsLocalRing

open AlgebraicGeometry.RelPicard
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_pts_relJacobian_jZero_of_representsRelSubPic_of_ratCurveModel
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))) c)

    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)
    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull p) g • Mη.pointEquivPlace x)

    (ρ : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ → (↥(GaloisRep.ratLocalizedAt ℓ) →+* ↥A))
    (hρ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ),
      A.subtype.comp (ρ A hA) = algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))
    (Ms : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      CurveModel (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) p))
    (es : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ), (Ms A hA).C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      ((residue ↥A).comp (ρ A hA)))))
    (hes_iso : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ), IsIso (es A hA))
    (hes : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ),
      es A hA ≫ pullback.snd c _ = (Ms A hA).toBase)

    (hsp : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
      [IsAlgClosed (ResidueField ↥A)],
      ∃ r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p) →
          Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) p),
        IsPlaceReductionModL A p r ∧
        ∀ (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ A hA))) c)
          (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
          (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C //
            q ≫ (Ms A hA).toBase = 𝟙 _}),
          x.1 ≫ eη ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1 →
          y.1 ≫ es A hA ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xA.1 →
          (Ms A hA).pointEquivPlace y = r (Mη.pointEquivPlace x))

    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull p))
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)
    (hcompat : ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (y : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
          pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))))
        (x₀ : closedPoints M₀.C),
      y ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      (y ≫ inv e₀).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x₀.1 →
      ((Mη.pointEquivPlace x).toValuationSubring.toSubring.comap
          ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p)).toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
              (B := ↥(modularFunctionFieldFull p))).toRingHom) =
        (M₀.placeOfPoint x₀).toValuationSubring.toSubring))

    (D : RelativePic0Designation ↥(GaloisRep.ratLocalizedAt ℓ) c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) (hgc : GeometricallyConnected D.toBase)
    :
    letI := heckeModuleBar p
    ∃ (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) D.toBase)
      (φ : HeckeAlg → SchemeHomOver D.toBase D.toBase),
      AbelianSchemePropertyBundle ↥(GaloisRep.ratLocalizedAt ℓ) D.toBase ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
        (x y : SchemeHomOver t D.toBase), (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul t x y = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul t y x) ∧
      (∀ x y : JZero p, pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul _ (pts x) (pts y)) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero p),
        (pts (σ • x)).1 =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1) ∧
      (∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
        ∃ (σA : Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
          (ptsA : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom A.subtype) ≫ σA) D.toBase)
          (ptsSp : JZeroC (ResidueField ↥A) p ≃
            SchemeHomOver (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ σA) D.toBase),
          (∀ x : JZero p, (ptsA x).1 = (pts x).1) ∧
          (∀ u v : JZeroC (ResidueField ↥A) p, ptsSp (u + v) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul _ (ptsSp u) (ptsSp v)) ∧
          (ReductionInputsModL A p → ReductionOfPointsAgreesModL p A D.toBase σA ptsA ptsSp)) ∧
      (∀ t : HeckeAlg,
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) (x y : SchemeHomOver s D.toBase),
          NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul s x y) (φ t) =
            (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul s (NeronModelInfra.schemeHomOverComp x (φ t))
              (NeronModelInfra.schemeHomOverComp y (φ t))) ∧
        ∀ x : JZero p, (pts (t • x)).1 = (pts x).1 ≫ (φ t).1) := by sorry
