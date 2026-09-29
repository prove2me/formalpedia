-- Prove2me | Theorems.Thm_ModularCurve_exists_functionField_degeneracyRoof_kaehlerToFunctionField_eq_correspondence_of_res_eq_heckeDiffBar
-- name    : ModularCurve.exists_functionField_degeneracyRoof_kaehlerToFunctionField_eq_correspondence_of_res_eq_heckeDiffBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/02766d33-4570-561f-b8ee-8257954f6846
-- title:
--   Degeneracy roof at the generic fibre: function-field Hecke correspondence
-- statement:
--   Fix $p \geq 1$ and a prime $\ell$ with $\ell \nmid p$, and write $R_\ell$ for the subring of $\mathbb{Q}$ of rationals whose denominator is coprime to $\ell$. Let $c \colon X \to \operatorname{Spec} R_\ell$ be proper, smooth of relative dimension $1$ and geometrically integral, let $\varepsilon$ be a section of $c$, let $D$ consist of a scheme $P$ with a structure morphism to $\operatorname{Spec} R_\ell$ and a zero section, and let $h$ assert that $D$ represents, via a Poincaré bundle with the usual universal property and triviality along the zero section, the subfunctor of $\varepsilon$-rigidified line bundles on $X$ that are fibrewise algebraically equivalent to zero; assume $D.\mathrm{toBase}$ smooth, proper and geometrically connected. Let $M_0$ be a curve model over $\mathbb{Q}$ of the field `modularFunctionFieldFull p` (an integral scheme, proper and smooth of relative dimension $1$ over $\mathbb{Q}$, with a specified isomorphism of that field onto its function field, a bijection between closed points and places, and the usual stalk and affineness conditions), and let $e_0$ be an isomorphism of $M_0.C$ onto the base change $X \times_{R_\ell} \mathbb{Q}$ compatible with the structure maps. Let $q$ be a prime, $M'$ a curve model over $\mathbb{Q}$ of `modularFunctionFieldFull (p * q)`, $\varphi_\alpha, \varphi_\beta$ ring homomorphisms between these two fields, and $\pi_\alpha, \pi_\beta \colon M'.C \to X$ morphisms over $\operatorname{Spec} R_\ell$ compatible with $M'.\mathrm{toBase}$. The hypothesis `hdeg` packages the roof data: $\pi_\alpha, \pi_\beta$ factor as $\pi_{\alpha 0}, \pi_{\beta 0} \colon M'.C \to M_0.C$ followed by $e_0$ and the first projection; both $\pi_{\alpha 0}, \pi_{\beta 0}$ lie over $\operatorname{Spec} \mathbb{Q}$ and are finite, flat and locally of finite presentation, $\pi_{\alpha 0}$ of constant fibre rank $d$; at generic points $\pi_{\alpha 0}, \pi_{\beta 0}$ induce $\varphi_\alpha, \varphi_\beta$ transported through the two model isomorphisms; and after base change to $\overline{\mathbb{Q}}$, $\varphi_\alpha$ and $\varphi_\beta$ agree with `heckeAlphaBar` and `heckeBetaBar` on elements $1 \otimes f$. Let $\mathcal{V} = (U_0, U_1)$ be a cover of $X$ by two affine opens with affine intersection, $\iota \colon \Gamma(X, U_0) \to$ `modularFunctionFieldBar p` a ring homomorphism compatible with the structure maps from $R_\ell$ through $\overline{\mathbb{Q}}$, assume the generic point of $M_0.C$ lies in the preimage of $U_0$, and assume $\iota$ is given, as a Laurent series over $\overline{\mathbb{Q}}$, by the germ at that generic point read through $M_0$'s field isomorphism and the coefficientwise embedding of Laurent series over $\mathbb{Q}$. Finally let $\mathrm{res}$ be an additive map from the degree-zero Čech cohomology $H^0$ of the Kähler sections of $\mathcal{V}$ (the kernel of the Čech difference) to $\Omega_{\mathrm{modularFunctionFieldBar}\, p/\overline{\mathbb{Q}}}$, given on each $\omega$ by applying [`KaehlerDifferential.mapOfRingHom`](def/AlgebraicGeometry_TwoAffineOpenCoverKaehler.html#L16) along $(R_\ell \to \overline{\mathbb{Q}}, \iota)$ to the $U_0$-component of $\omega$. The conclusion asserts the existence of the following data and properties for the generic fibre $X_q = X \times_{R_\ell} \mathbb{Q}$ with structure map $c_q$: $X_q$ is integral, $c_q$ is separated and smooth of relative dimension $1$, every proper closed subset of $X_q$ is finite, $X_q$'s function field is a one-variable function field over $\mathbb{Q}$ (principal divisors exist, places have finite residue extensions, the module of Kähler differentials is free of rank one) in which every place's canonical coordinate differential spans, with nontrivial differentials, a canonical divisor and the residue theorem; $M'.C$ is integral; the induced morphisms $M'.C \to X_q$ obtained from $\pi_\alpha$ and $\pi_\beta$ are, respectively, finite, flat and locally of finite presentation with all fibre ranks equal to $d$, and affine; there are $\mathbb{Q}$-algebra maps $\varphi'_\alpha, \varphi'_\beta \colon X_q$'s function field $\to M'.C$'s function field inducing those two morphisms on generic stalks; $M'.C$'s function field satisfies the same curve, coordinate-differential, canonical-divisor, principal-divisor and residue-theorem conditions; $\varphi'_\alpha, \varphi'_\beta$ are integral, $\varphi'_\alpha$ satisfies the trace-integrality condition (traces of elements integral at all places above $v$ are integral at $v$), $M'.C$'s function field is separable over $X_q$'s along $\varphi'_\beta$, both satisfy the fibrewise residue identity, and $U_0$ pulled back to $X_q$ is nonempty; and then, for all $\omega, \omega'$ in that $H^0$ with $\mathrm{res}\, \omega' =$ `heckeDiffBar p q` $(\mathrm{res}\, \omega)$, writing $\omega_\eta$ for the differential on $X_q$'s function field obtained from the $U_0$-component of the base change of $\omega$ via `kaehlerToFunctionField`, the pullback of $\omega_\eta$ along $\varphi'_\alpha$ is a regular differential on $M'.C$'s function field (at every place of the form $f \cdot \mathrm{dCoord}$ with $f$ in the valuation ring), and $\omega'_\eta$ equals the trace along $\varphi'_\beta$ of the pullback of $\omega_\eta$ along $\varphi'_\alpha$.
--
--   This is the packaging statement that reads the degeneracy correspondence computing the Hecke operator $T_q$ on $X_0(p)$ at the generic fibre of an $R_\ell$-model as data about one-variable function fields over $\mathbb{Q}$: two embeddings of the function field of the $p$-level model into that of the $pq$-level model, the residue calculus (local residues, residue theorem, trace identity on fibres) needed to compare differentials along them, and the identity expressing a $T_q$-eigenform relation on Čech $H^0$ as a trace-of-pullback identity. It is used in the comparison of the integral Serre pairing with Hecke generators on deformation classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_functionField_degeneracyRoof_kaehlerToFunctionField_eq_correspondence_of_res_eq_heckeDiffBar.lean

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
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_ModularCurve_HeckeProj
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_RigKerDualNumber
import Definitions.Def_AlgebraicGeometry_RelPicardStageHom
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import Definitions.Def_AlgebraicGeometry_TwoChartCechSerrePairingInt
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_CechH1PushPull
import Definitions.Def_AlgebraicCurve_KaehlerToFunctionField
import Definitions.Def_AlgebraicCurve_SerrePairing
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_FibreResidueIdentityAlong
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian ModularCurve AlgebraicCurve IsLocalRing CuspForm Scheme.TwoAffineOpenCover KaehlerDifferential

theorem ModularCurve.exists_functionField_degeneracyRoof_kaehlerToFunctionField_eq_correspondence_of_res_eq_heckeDiffBar
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))) c)
    (D : RelativePic0Designation ↥(GaloisRep.ratLocalizedAt ℓ) c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) (hgc : GeometricallyConnected D.toBase)

    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull p))
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)

    (q : Nat.Primes) [NeZero (q : ℕ)] [NeZero (p * (q : ℕ))]

    (M' : CurveModel ℚ ↥(modularFunctionFieldFull (p * (q : ℕ))))
    (φα φβ : ↥(modularFunctionFieldFull p) →+* ↥(modularFunctionFieldFull (p * (q : ℕ))))
    (πα πβ : M'.C ⟶ X)
    (Hα : πα ≫ c = M'.toBase ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ) (Hβ : πβ ≫ c = M'.toBase ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)
    (πα₀ πβ₀ : M'.C ⟶ M₀.C) (d : ℕ)
    (hdeg :
      πα = πα₀ ≫ e₀ ≫ pullback.fst c _ ∧ πβ = πβ₀ ≫ e₀ ≫ pullback.fst c _ ∧
      πα₀ ≫ M₀.toBase = M'.toBase ∧ πβ₀ ≫ M₀.toBase = M'.toBase ∧
      IsFinite πα₀ ∧ Flat πα₀ ∧ LocallyOfFinitePresentation πα₀ ∧
      IsFinite πβ₀ ∧ Flat πβ₀ ∧ LocallyOfFinitePresentation πβ₀ ∧
      (∀ x, πα₀.finrank x = d) ∧

      M'.C.fromSpecStalk (genericPoint M'.C) ≫ πα₀ =
        Spec.map (CommRingCat.ofHom (M'.ffEquiv.toRingHom.comp (φα.comp M₀.ffEquiv.symm.toRingHom))) ≫
          M₀.C.fromSpecStalk (genericPoint M₀.C) ∧
      M'.C.fromSpecStalk (genericPoint M'.C) ≫ πβ₀ =
        Spec.map (CommRingCat.ofHom (M'.ffEquiv.toRingHom.comp (φβ.comp M₀.ffEquiv.symm.toRingHom))) ≫
          M₀.C.fromSpecStalk (genericPoint M₀.C) ∧
      (∀ f : ↥(modularFunctionFieldFull p),
        heckeAlphaBar (AlgebraicClosure ℚ) p q (baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p) (1 ⊗ₜ f)) =
          baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull (p * (q : ℕ))) (1 ⊗ₜ φα f)) ∧
      (∀ f : ↥(modularFunctionFieldFull p),
        heckeBetaBar (AlgebraicClosure ℚ) p q (baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p) (1 ⊗ₜ f)) =
          baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull (p * (q : ℕ))) (1 ⊗ₜ φβ f)))

    (𝒱 : X.TwoAffineOpenCover)

    (ι : (𝒱.cover c).A0 →+* ↥(modularFunctionFieldBar p))
    (hιR : ι.comp (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (𝒱.cover c).A0) =
      (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))
    (hgen0 : genericPoint M₀.C ∈ (e₀ ≫ pullback.fst c _) ⁻¹ᵁ 𝒱.U0)
    (hιdef : ∀ a : (𝒱.cover c).A0, ((ι a : ↥(modularFunctionFieldBar p)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (((M₀.ffEquiv.symm ((M₀.C.presheaf.germ ((e₀ ≫ pullback.fst c _) ⁻¹ᵁ 𝒱.U0) (genericPoint M₀.C) hgen0).hom (((e₀ ≫ pullback.fst c _).app (𝒱.U0)).hom a))) : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))
    (res : ↥((𝒱.kaehlerSections c).H0) →+ Ω[modularFunctionFieldBar p⁄AlgebraicClosure ℚ])
    (hres : ∀ ω : ↥((𝒱.kaehlerSections c).H0),
      res ω = KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)) ι hιR ω.val.1) :
    letI Rℓ := ↥(GaloisRep.ratLocalizedAt ℓ)
    letI Xq := Limits.pullback c (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)
    letI cq : Xq ⟶ Spec (.of ℚ) := pullback.snd c (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)
    letI := (AlgebraicCurve.baseToFunctionField cq).toAlgebra
    letI := (AlgebraicCurve.baseToFunctionField M'.toBase).toAlgebra
    letI Vq := 𝒱.pullback c ℚ
    letI fq := HomOver.baseChange 𝒱 c ℚ
    ∃ (_ : IsIntegral Xq) (_ : IsSeparated cq) (_ : SmoothOfRelativeDimension 1 cq)

      (_ : ∀ Z : Set Xq, IsClosed Z → Z ≠ Set.univ → Z.Finite)
      (_ : AlgebraicCurve.IsCurveOver ℚ Xq.functionField)
      (_ : ∀ v : AlgebraicCurve.Place ℚ Xq.functionField, v.DCoordGenerates)
      (_ : Nontrivial Ω[Xq.functionField⁄ℚ])
      (_ : AlgebraicCurve.HasCanonicalDivisor (K := ℚ) (F := Xq.functionField))
      (hRTq : AlgebraicCurve.ResidueTheorem ℚ Xq.functionField)
      (_ : IsIntegral M'.C)
      (_ : IsFinite (pullback.lift πα M'.toBase Hα : M'.C ⟶ Xq))
      (_ : Flat (pullback.lift πα M'.toBase Hα : M'.C ⟶ Xq))
      (_ : LocallyOfFinitePresentation (pullback.lift πα M'.toBase Hα : M'.C ⟶ Xq))
      (_ : IsAffineHom (pullback.lift πβ M'.toBase Hβ : M'.C ⟶ Xq))
      (_ : ∀ z, (pullback.lift πα M'.toBase Hα : M'.C ⟶ Xq).finrank z = d)
      (φα' φβ' : Xq.functionField →ₐ[ℚ] M'.C.functionField)
      (_ : M'.C.fromSpecStalk (genericPoint M'.C) ≫ pullback.lift πα M'.toBase Hα =
        Spec.map (CommRingCat.ofHom φα'.toRingHom) ≫ Xq.fromSpecStalk (genericPoint Xq))
      (_ : M'.C.fromSpecStalk (genericPoint M'.C) ≫ pullback.lift πβ M'.toBase Hβ =
        Spec.map (CommRingCat.ofHom φβ'.toRingHom) ≫ Xq.fromSpecStalk (genericPoint Xq))
      (_ : AlgebraicCurve.IsCurveOver ℚ M'.C.functionField)
      (_ : ∀ w : AlgebraicCurve.Place ℚ M'.C.functionField, w.DCoordGenerates)
      (_ : Nontrivial Ω[M'.C.functionField⁄ℚ])
      (_ : AlgebraicCurve.HasCanonicalDivisor (K := ℚ) (F := M'.C.functionField))
      (_ : AlgebraicCurve.HasPrincipalDivisors ℚ M'.C.functionField)
      (_ : AlgebraicCurve.ResidueTheorem ℚ M'.C.functionField)
      (hφα : φα'.toRingHom.IsIntegral) (hφβ : φβ'.toRingHom.IsIntegral)
      (_ : AlgebraicCurve.TraceIntegralAlong φα' hφα) (_ : AlgebraicCurve.SeparableAlong ℚ φβ')
      (_ : AlgebraicCurve.FibreResidueIdentityAlong φα' hφα) (_ : AlgebraicCurve.FibreResidueIdentityAlong φβ' hφβ)
      (_ : Nonempty (Vq.U0 : Xq.Opens)),
      ∀ (ω ω' : ↥((𝒱.kaehlerSections c).H0)), res ω' = heckeDiffBar p q (res ω) →
        AlgebraicCurve.Differential.pullbackAlong φα'
            (AlgebraicCurve.kaehlerToFunctionField cq Vq.U0 (fq.kaehlerH0map ω).val.1) ∈
          AlgebraicCurve.regularDifferentials ℚ M'.C.functionField ∧
        AlgebraicCurve.kaehlerToFunctionField cq Vq.U0 (fq.kaehlerH0map ω').val.1 =
          AlgebraicCurve.Differential.correspondence φβ' φα'
            (AlgebraicCurve.kaehlerToFunctionField cq Vq.U0 (fq.kaehlerH0map ω).val.1) := by sorry
