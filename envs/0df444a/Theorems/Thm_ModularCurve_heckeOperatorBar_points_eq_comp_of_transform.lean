-- Prove2me | Theorems.Thm_ModularCurve_heckeOperatorBar_points_eq_comp_of_transform
-- name    : ModularCurve.heckeOperatorBar_points_eq_comp_of_transform
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/0e8eb103-56f1-5e8f-b25b-ed38e3032b22
-- title:
--   Norm transform endomorphism realises T_q on ℚ̄-points
-- statement:
--   Fix a positive integer $p$ and a prime $\ell$ with $\ell \nmid p$, and write $R$ for the subring [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) of $\mathbf{Q}$ consisting of those rationals whose denominator is coprime to $\ell$.
--
--   *Curve and Picard data.* Let $c : X \to \operatorname{Spec} R$ be proper, smooth of relative dimension $1$ and geometrically integral, let $\varepsilon$ be a section of $c$ (an element of `SchemeHomOver (𝟙 (Spec R)) c`, i.e. a morphism $\operatorname{Spec} R \to X$ whose composite with $c$ is the identity), and let $D$ be a `RelativePic0Designation` for $c$: a scheme $P$ together with a structure morphism $D.\mathrm{toBase} : P \to \operatorname{Spec} R$ and a section `D.zeroSection` of it. The hypothesis $h$ asserts `RepresentsRelSubPic c ε (algEquivZeroCut c ε) D`, that is: a rigidified line bundle `h.poincare` on $X \times_R P$ (a line bundle on the fibre product whose restriction along the rigidifying section is trivial) whose class satisfies the cut `algEquivZeroCut`, namely that for every algebraically closed field $k$ and every $k$-point of the base the restriction to the corresponding geometric fibre is algebraically equivalent to zero; the universal property that for every $t : T \to \operatorname{Spec} R$ and every rigidified line bundle $M$ on $X \times_R T$ satisfying the same fibrewise condition there is a unique $T$-morphism $T \to P$ along which the Poincaré bundle pulls back to $M.L$; and the triviality of the pullback of the Poincaré bundle along `D.zeroSection`. The hypotheses `hsm`, `hpr`, `hgc` require $D.\mathrm{toBase}$ to be smooth, proper and geometrically connected.
--
--   *Abel–Jacobi data.* Let $aj : X \to P$ be a morphism over $\operatorname{Spec} R$ with `hajε`: $\varepsilon$ followed by $aj$ equals `D.zeroSection`. The hypothesis `haj` requires that for every field $K$, every $t : \operatorname{Spec} K \to \operatorname{Spec} R$ and every $K$-point $x$ of $X$ over $t$, the pullback of the Poincaré bundle along $x$ followed by $aj$ be isomorphic to the tensor product of the `lineBundle` of the relative effective Cartier divisor `RelEffCartierDiv.ofPoint` attached to $x$ (the dual of the ideal sheaf of the graph of $x$) with the `idealModule` of the divisor attached to $t$ followed by $\varepsilon$ (the ideal sheaf of the graph of the base point); in classical notation, $aj$ classifies $\mathcal{O}(\Gamma_x) \otimes \mathcal{O}(-\varepsilon)$ pointwise.
--
--   *Identification of the geometric generic fibre at level $p$.* Let $M_\eta$ be a `CurveModel` over $\overline{\mathbf{Q}}$ for `modularFunctionFieldBar p`, the base change to $\overline{\mathbf{Q}}$ of the level-$p$ modular function field inside Laurent series; thus $M_\eta$ consists of an integral scheme with a proper, smooth relative dimension one structure morphism to $\operatorname{Spec}\overline{\mathbf{Q}}$, an identification of its function field with that field compatible with the base, and a bijection `placeOfPoint` between its closed points and the places of the function field over $\overline{\mathbf{Q}}$ matching valuation subrings with stalks. Let $e_\eta$ be an isomorphism from $M_\eta.C$ onto $X \times_R \overline{\mathbf{Q}}$ with `heη`: $e_\eta$ followed by the second projection equals $M_\eta.\mathrm{toBase}$. The hypothesis `hgal` requires Galois equivariance of this identification: for every $g \in \overline{\mathbf{Q}} \simeq_{\mathbf{Q}\text{-alg}} \overline{\mathbf{Q}}$ and all $\overline{\mathbf{Q}}$-points $x, x'$ of $M_\eta.C$, if $x'$ followed by $e_\eta$ and the first projection to $X$ equals $\operatorname{Spec}(g)$ followed by $x$, $e_\eta$ and the first projection, then `Mη.pointEquivPlace x'` equals the action of `arithmeticGalois (modularFunctionFieldFull p) g` on `Mη.pointEquivPlace x`.
--
--   *Level $p\,q$.* Let $q$ be a prime, with $q \neq 0$ and $p q \neq 0$ in the relevant `NeZero` sense.
--
--   *Descent of the Picard data to $\mathbf{Q}$.* The hypothesis `hℚ` asserts `RepresentsRelSubPic` for the base change $c_{\mathbf{Q}} : X_{\mathbf{Q}} \to \operatorname{Spec}\mathbf{Q}$, the base-changed section `sectionBaseChange ℚ ε`, the corresponding cut `algEquivZeroCut`, and `D.baseChange ℚ` (whose total space is $P \times_{\operatorname{Spec} R} \operatorname{Spec}\mathbf{Q}$ with the evident zero section). The hypothesis `hP` requires the Poincaré bundle of `hℚ` to be isomorphic to the transport `BaseChange.ofR` of the pullback of `h.poincare` along the first projection $P \times_R \mathbf{Q} \to P$.
--
--   *The correspondence.* Let $Y$ be a scheme with $c_Y : Y \to \operatorname{Spec}\mathbf{Q}$ and two morphisms $\pi_\alpha, \pi_\beta : Y \to X_{\mathbf{Q}}$ over $\mathbf{Q}$ (hypotheses `hα`, `hβ`), both finite, flat and locally of finite presentation, and let $d$ be a natural number with `hdα`: the fibre rank of $\pi_\alpha$ equals $d$ at every point. No analogous constancy of degree is imposed on $\pi_\beta$.
--
--   *The transform $\Phi$ and the endomorphism $\varphi_\eta$.* Let $\Phi$ assign, to every $t : T \to \operatorname{Spec}\mathbf{Q}$, a self-map of the rigidified line bundles on $X_{\mathbf{Q}} \times_{\mathbf{Q}} T$ rigidified along the base-changed section. The hypothesis `hΦ` requires $(\Phi\, t\, M).L$ to be isomorphic to the rigidification, along the rigidifying section and the projection $X_{\mathbf{Q}} \times_{\mathbf{Q}} T \to T$, of `Scheme.Modules.normModule` of degree $d$ along $\pi_\alpha \times T$ applied to the pullback of $M.L$ along $\pi_\beta \times T$; here `normModule π d L` is $\det_d(\pi_* L) \otimes \det_d(\pi_* \mathcal{O})^{\vee}$. The hypothesis `hcut` requires $\Phi$ to preserve the fibrewise algebraic-equivalence-to-zero cut. Let $\varphi_\eta$ be an endomorphism of $(D.\mathrm{baseChange}\ \mathbf{Q}).\mathrm{toBase}$ over $\operatorname{Spec}\mathbf{Q}$ such that `hφη`: for every $t$, every rigidified line bundle $M$ and every proof $hM$ that $M$ satisfies the cut, the classifying morphism `hℚ.classify t M hM` followed by $\varphi_\eta$ equals `hℚ.classify t (Φ t M) (hcut t M hM)`; and `hφadd`: composition with $\varphi_\eta$ is additive for the relative group law obtained from `hℚ` through `algEquivZeroGroupCut`, i.e. the product of two points composed with $\varphi_\eta$ equals the product of their composites with $\varphi_\eta$.
--
--   *Identification at level $p q$ and the degeneracy maps on places.* Let $M_\eta'$ be a `CurveModel` over $\overline{\mathbf{Q}}$ for `modularFunctionFieldBar (p * q)`, and $e_\eta'$ an isomorphism from $M_\eta'.C$ onto $Y \times_{\mathbf{Q}} \overline{\mathbf{Q}}$ with `heη'`: $e_\eta'$ followed by the second projection equals $M_\eta'.\mathrm{toBase}$. The hypotheses `hαI`, `hβI` require the degeneracy embeddings `heckeAlphaBar (AlgebraicClosure ℚ) p q` and `heckeBetaBar (AlgebraicClosure ℚ) p q` of the level-$p$ modular function field over $\overline{\mathbf{Q}}$ into the level-$pq$ one to be integral ring homomorphisms. The hypotheses `hplaceα` and `hplaceβ` require compatibility of the two projections with restriction of places: for all $\overline{\mathbf{Q}}$-points $y$ of $M_\eta'.C$ and $x$ of $M_\eta.C$, if $y$ followed by $e_\eta'$, the first projection, $\pi_\alpha$ (respectively $\pi_\beta$) and the first projection to $X$ equals $x$ followed by $e_\eta$ and the first projection, then `Mη.pointEquivPlace x` equals the restriction `Place.restrictAlong` of `Mη'.pointEquivPlace y` along `heckeAlphaBar` (respectively `heckeBetaBar`).
--
--   *The parametrisation of points by divisor classes.* Let `pts` be a bijection from `JZero p`, the group $\operatorname{Pic}^0$ of degree-zero divisor classes of `modularFunctionFieldBar p` over $\overline{\mathbf{Q}}$, onto the $\overline{\mathbf{Q}}$-points of $D.\mathrm{toBase}$ over the structure map $\operatorname{Spec}\overline{\mathbf{Q}} \to \operatorname{Spec} R$. The hypothesis `hadd` requires `pts` to be additive for the relative group law attached to $h$ through `algEquivZeroGroupCut`. The hypothesis `hnorm` requires the normalisation: for all $\overline{\mathbf{Q}}$-points $x$ and $s$ of $M_\eta.C$ such that $s$ followed by $e_\eta$ and the first projection is the base point $\varepsilon$ over $\overline{\mathbf{Q}}$, there exists a degree-zero divisor $D_v$ equal to $[\,\mathrm{place}(x)\,] - [\,\mathrm{place}(s)\,]$ whose class satisfies: the underlying morphism of `pts (Pic0.mk Dv)` equals $x$ followed by $e_\eta$, the first projection and $aj$.
--
--   *Conclusion.* Let $x$ be an element of `JZero p` and let $z$, $z_q$ be $\overline{\mathbf{Q}}$-points of $(D.\mathrm{baseChange}\ \mathbf{Q}).\mathrm{toBase}$ such that $z$ followed by the first projection $P \times_R \mathbf{Q} \to P$ equals the underlying morphism of `pts x` (hypothesis `hz`), and $z_q$ followed by the same projection equals the underlying morphism of `pts (heckeOperatorBar p q x)`, where `heckeOperatorBar p q` is the Hecke operator at $q$ on `JZero p` (hypothesis `hzq`). Then the underlying morphism of $z_q$ equals that of $z$ followed by $\varphi_\eta$.
--
--   This is the computation on $\overline{\mathbf{Q}}$-points identifying the endomorphism of the generic fibre of the relative Jacobian, obtained from the transform "norm along $\pi_\alpha$ of pull-back along $\pi_\beta$" by the universal property of the representing scheme, with the Hecke operator $T_q$ on degree-zero divisor classes of the level-$p$ modular curve. It is used by [`ModularCurve.exists_heckeEndomorphism_relJacobian_of_representsRelSubPic_of_ratCurveModel`](thm.html#ModularCurve.exists_heckeEndomorphism_relJacobian_of_representsRelSubPic_of_ratCurveModel), by [`ModularCurve.exists_heckeEndomorphism_relJacobian_moduli_of_ratCurveModel`](thm.html#ModularCurve.exists_heckeEndomorphism_relJacobian_moduli_of_ratCurveModel) and by [`ModularCurve.forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage`](thm.html#ModularCurve.forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage), where the Hecke correspondence is shown to act on the relative Jacobian over the localisation of $\mathbf{Z}$ at $\ell$ by a scheme endomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeOperatorBar_points_eq_comp_of_transform.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian ModularCurve AlgebraicCurve AlgebraicGeometry.SmoothProperCurve
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.heckeOperatorBar_points_eq_comp_of_transform
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))) c)
    (D : RelativePic0Designation ↥(GaloisRep.ratLocalizedAt ℓ) c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) (hgc : GeometricallyConnected D.toBase)
    (aj : SchemeHomOver c D.toBase) (hajε : ε.1 ≫ aj.1 = D.zeroSection)
    (haj : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) (x : SchemeHomOver t c),
        Nonempty ((h.poincare.pullbackAlong
            ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))

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
    (q : Nat.Primes) [NeZero (q : ℕ)] [NeZero (p * (q : ℕ))]

    (hℚ : RepresentsRelSubPic (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)
      (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)) (D.baseChange ℚ))
    (hP : Nonempty (hℚ.poincare.L ≅ (BaseChange.ofR c ε ℚ
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ), pullback.condition⟩)).L))

    (Y : Scheme.{0}) (cY : Y ⟶ Spec (CommRingCat.of ℚ))
    (πα πβ : Y ⟶ pullback c (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))
    (hα : πα ≫ baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ = cY)
    (hβ : πβ ≫ baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ = cY)
    [IsFinite πα] [Flat πα] [LocallyOfFinitePresentation πα]
    [IsFinite πβ] [Flat πβ] [LocallyOfFinitePresentation πβ]
    (d : ℕ) (hdα : ∀ y, πα.finrank y = d)

    (Φ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ)),
      RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t →
        RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t)
    (hΦ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ))
        (M : RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t),
      Nonempty ((Φ t M).L ≅ Scheme.Modules.rigidify
        (rigSection (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) t (sectionBaseChange ℚ ε))
        (pullback.snd (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) t)
        (Scheme.Modules.normModule (curveChange πα hα t) d
          ((Scheme.Modules.pullback (curveChange πβ hβ t)).obj M.L))))
    (hcut : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ))
        (M : RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t),
      (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)).P t M →
        (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)).P t (Φ t M))
    (φη : SchemeHomOver (D.baseChange ℚ).toBase (D.baseChange ℚ).toBase)
    (hφη : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ))
        (M : RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t)
        (hM : (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)).P t M),
      postComp φη (hℚ.classify t M hM) = hℚ.classify t (Φ t M) (hcut t M hM))
    (hφadd : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℚ)) (x y : SchemeHomOver s (D.baseChange ℚ).toBase),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw
            (P := algEquivZeroGroupCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)) hℚ).mul s x y) φη =
        (RepresentsRelSubPic.relativeGroupLaw
            (P := algEquivZeroGroupCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)) hℚ).mul s
          (NeronModelInfra.schemeHomOverComp x φη) (NeronModelInfra.schemeHomOverComp y φη))

    (Mη' : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * (q : ℕ))))
    (eη' : Mη'.C ⟶ pullback cY (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) [IsIso eη']
    (heη' : eη' ≫ pullback.snd _ _ = Mη'.toBase)
    (hαI : (heckeAlphaBar (AlgebraicClosure ℚ) p q).toRingHom.IsIntegral)
    (hβI : (heckeBetaBar (AlgebraicClosure ℚ) p q).toRingHom.IsIntegral)
    (hplaceα : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη'.C // q ≫ Mη'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      y.1 ≫ eη' ≫ pullback.fst cY _ ≫ πα ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x =
        Place.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) p q) hαI (Mη'.pointEquivPlace y))
    (hplaceβ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη'.C // q ≫ Mη'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      y.1 ≫ eη' ≫ pullback.fst cY _ ≫ πβ ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x =
        Place.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) p q) hβI (Mη'.pointEquivPlace y))

    (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) D.toBase)
    (hadd : ∀ x y : JZero p,
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul _ (pts x) (pts y))
    (hnorm : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ eη ≫ pullback.fst c _ ≫ aj.1)

    (x : JZero p)
    (z zq : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) (D.baseChange ℚ).toBase)
    (hz : z.1 ≫ pullback.fst D.toBase (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ) = (pts x).1)
    (hzq : zq.1 ≫ pullback.fst D.toBase (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ) = (pts (heckeOperatorBar p q x)).1) :
    zq.1 = z.1 ≫ φη.1 := by sorry
