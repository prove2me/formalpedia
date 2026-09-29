-- Prove2me | Theorems.Thm_ModularCurve_serrePairingInt_deformationClass_heckeGen_eq_of_isCompletionAlong_of_res_eq_heckeDiffBar
-- name    : ModularCurve.serrePairingInt_deformationClass_heckeGen_eq_of_isCompletionAlong_of_res_eq_heckeDiffBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/ca3002a8-bf70-5425-8fc2-831f2268a4a7
-- title:
--   Hecke adjunction for the integral Serre pairing, sectional charts
-- statement:
--   Throughout, $p$ is a natural number, $\ell$ a prime with $\ell \nmid p$ (the hypothesis `hℓp`), and $R$ denotes the subring [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) of $\mathbf{Q}$ consisting of those rationals whose denominator is coprime to $\ell$.
--
--   **Curve and Picard data.** $c : X \to \operatorname{Spec} R$ is proper, smooth of relative dimension $1$ and geometrically integral, and $\varepsilon$ is a section of $c$ (a morphism $\operatorname{Spec} R \to X$ over the identity of $\operatorname{Spec} R$). $D$ is a `RelativePic0Designation` for $c$, i.e. a scheme together with a structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec} R$ and a section $D.\mathrm{zeroSection}$ of it. The datum $h$ asserts that $D$ represents the relative Picard condition `algEquivZeroCut c ε`: it consists of a Poincaré rigidified line bundle on $X \times_R D$ satisfying the condition that over every point with values in an algebraically closed field the restriction to the corresponding fibre is algebraically equivalent to zero, of the universal property that for every $t : T \to \operatorname{Spec} R$ and every rigidified line bundle $M$ on $X \times_R T$ satisfying that condition there is a unique $T$-point of $D$ over $\operatorname{Spec} R$ along which the Poincaré bundle pulls back to a bundle isomorphic to $M.L$, and of a trivialisation of the pullback of the Poincaré bundle along the zero section. The hypotheses `hsm`, `hpr`, `hgc` say that $D.\mathrm{toBase}$ is smooth, proper and geometrically connected. An Abel–Jacobi morphism is given: $aj$ is a morphism $X \to D$ over $\operatorname{Spec} R$ with $\varepsilon$ followed by $aj$ equal to the zero section (`hajε`), and `haj` states that for every field $K$, every $t : \operatorname{Spec} K \to \operatorname{Spec} R$ and every $K$-point $x$ of $X$ over $t$, the pullback of the Poincaré bundle along $x$ followed by $aj$ is isomorphic to the tensor product of the line bundle of the relative effective Cartier divisor of the point $x$ (the dual of the ideal sheaf of the graph of $x$ in $X \times_R \operatorname{Spec} K$) with the ideal module of the relative effective Cartier divisor of the point $t$ followed by $\varepsilon$.
--
--   **Models of the generic fibre.** $M_\eta$ is a curve model over $\overline{\mathbf{Q}}$ whose function field is identified with `modularFunctionFieldBar p`, the subfield of $\overline{\mathbf{Q}}((T))$ generated over $\overline{\mathbf{Q}}$ by the coefficientwise image of the level-$p$ modular function field `modularFunctionFieldFull p` $\subseteq \mathbf{Q}((T))$; $e_\eta$ is an isomorphism of $M_\eta.C$ with $X \times_R \overline{\mathbf{Q}}$ compatible with the structure morphisms (`heη`). The hypothesis `hgal` is a Galois equivariance: for every $g \in \operatorname{Aut}_{\mathbf{Q}}(\overline{\mathbf{Q}})$ and all $\overline{\mathbf{Q}}$-sections $x, x'$ of $M_\eta.\mathrm{toBase}$, if $x'$ followed by $e_\eta$ and the projection to $X$ equals $\operatorname{Spec}(g)$ followed by $x$ followed by $e_\eta$ and that projection, then the place of `modularFunctionFieldBar p` attached to $x'$ by the bijection `Mη.pointEquivPlace` is the translate of the place attached to $x$ under the semilinear automorphism `arithmeticGalois (modularFunctionFieldFull p) g` of `modularFunctionFieldBar p`, which acts coefficientwise by $g$ and acts on the places of that field. Likewise $M_0$ is a curve model over $\mathbf{Q}$ with function field `modularFunctionFieldFull p` and $e_0$ an isomorphism of $M_0.C$ with $X \times_R \mathbf{Q}$ compatible with the structure morphisms (`he₀`). The hypothesis `hcompat` compares places: for every $\overline{\mathbf{Q}}$-section $x$ of $M_\eta.\mathrm{toBase}$, every $\overline{\mathbf{Q}}$-point $y$ of $X \times_R \mathbf{Q}$ and every closed point $x_0$ of $M_0.C$, if $y$ and $x$ followed by $e_\eta$ have the same image in $X$, and if $y$ transported through $e_0^{-1}$ sends the closed point of $\operatorname{Spec}\overline{\mathbf{Q}}$ to $x_0$, then the valuation subring of the place of $x$, pulled back along the embedding of `modularFunctionFieldFull p` into `modularFunctionFieldBar p` given by $f \mapsto 1 \otimes f$ followed by `baseChangeEquiv`, coincides with the valuation subring of `M₀.placeOfPoint x₀`.
--
--   **Degeneracy data at $q$.** $q$ is a prime. $M'$ is a curve model over $\mathbf{Q}$ with function field `modularFunctionFieldFull (p * q)`; $\varphi_\alpha, \varphi_\beta$ are ring homomorphisms from `modularFunctionFieldFull p` to `modularFunctionFieldFull (p * q)`; $\pi_\alpha, \pi_\beta : M'.C \to X$ satisfy $\pi_\alpha$ followed by $c$, and $\pi_\beta$ followed by $c$, equal $M'.\mathrm{toBase}$ followed by $\operatorname{Spec}$ of $R \to \mathbf{Q}$ (hypotheses `Hα`, `Hβ`); $\pi_{\alpha 0}, \pi_{\beta 0} : M'.C \to M_0.C$ and $d \in \mathbf{N}$ are further data. The hypothesis `hdeg` is a conjunction of fifteen clauses, summarised here: $\pi_\alpha$ and $\pi_\beta$ factor as $\pi_{\alpha 0}$, resp. $\pi_{\beta 0}$, followed by $e_0$ and the projection to $X$; $\pi_{\alpha 0}$ and $\pi_{\beta 0}$ are morphisms over $\operatorname{Spec} \mathbf{Q}$; each of them is finite, flat and locally of finite presentation; $\pi_{\alpha 0}$ has fibre rank $d$ at every point; on generic points, $\pi_{\alpha 0}$ and $\pi_{\beta 0}$ are induced by $\varphi_\alpha$ and $\varphi_\beta$ through the function-field identifications `M'.ffEquiv` and `M₀.ffEquiv`; and, after base change to $\overline{\mathbf{Q}}$, $\varphi_\alpha$ and $\varphi_\beta$ agree on elements $1 \otimes f$ with the degeneracy embeddings `heckeAlphaBar (AlgebraicClosure ℚ) p q` and `heckeBetaBar (AlgebraicClosure ℚ) p q` respectively.
--
--   **The endomorphism $\varphi_1$.** $\varphi_1$ is an endomorphism of $D$ over $\operatorname{Spec} R$. The hypothesis `hφ₁` says that $\varphi_1$ is a homomorphism for the relative group law attached by $h$ to the group condition `algEquivZeroGroupCut c ε`: for every $T$, every $s : T \to \operatorname{Spec} R$ and all $T$-points $x, y$ of $D$ over $s$, the product $x \cdot y$ followed by $\varphi_1$ equals the product of $x$ followed by $\varphi_1$ and $y$ followed by $\varphi_1$. The hypothesis `hmoduli` describes $\varphi_1$ on points over $\mathbf{Q}$ in moduli terms: for every $T$, every $t' : T \to \operatorname{Spec}\mathbf{Q}$ and every rigidified line bundle $M$ on $X \times_R T$ over $t'$ followed by $\operatorname{Spec}$ of $R \to \mathbf{Q}$ satisfying the fibrewise algebraic-equivalence-to-zero condition, the pullback of the Poincaré bundle along the classifying point of $M$ followed by $\varphi_1$ is isomorphic to the rigidification, along the rigidifying section and relative to the projection, of the rank-$d$ norm module along the curve change of $\pi_\alpha$ of the pullback along the curve change of $\pi_\beta$ of $M.L$; here the norm module of a module along a morphism is $\det_d$ of its pushforward tensored with the dual of $\det_d$ of the pushforward of the unit.
--
--   **Cover, charts and sections.** $\mathcal{V}$ is a two-affine open cover of $X$ (affine opens $U_0, U_1$ with affine intersection and $U_0 \sqcup U_1 = \top$), so that the associated Čech cover over $R$ has rings $A_0 = \Gamma(X, U_0)$, $A_1 = \Gamma(X, U_1)$, $A_{01} = \Gamma(X, U_0 \cap U_1)$ with the two restriction maps. For a finite index type $\iota_T$, $\Lambda$ assigns to each $i$ a Laurent chart, i.e. a ring homomorphism $A_{01} \to R((T))$ carrying constants to constants; `hv` asserts that the sum of the residues of the $\Lambda_i$ annihilates the image of the Čech differential on the Kähler sections, so that the integral Serre pairing `serrePairingInt Λ hv`, the trace pairing of the cup product against the residue sum, is defined from $H^0$ of the Kähler sections and $H^1$ of the structure sheaf sections to $R$. The family $\sigma : \iota_T \to (\operatorname{Spec} R \to X)$ is sectional (`hσ`): each $\sigma_i$ is a section of $c$ with image inside $U_0$, the complement of $U_1$ is the union of the images of the $\sigma_i$, and these images are pairwise disjoint. The hypothesis `hΛ` says that each $\Lambda_i$ is a completion along the restriction $A_0 \to A_{01}$ with respect to the evaluation algebra map of $\sigma_i$: expansions of elements of $A_0$ are power series, every finite truncation of a power series is realised by an element of $A_0$, and the vanishing of the first $n$ coefficients of the expansion of $a \in A_0$ is equivalent to $a$ lying in the $n$-th power of the kernel of evaluation at $\sigma_i$. The hypothesis `hΛt` says that each $\Lambda_i$ has a parameter on $A_0$: some element of $A_0$ has expansion $T$.
--
--   **Deformation classes and the expansion map.** $\delta$ assigns to each class of rigidified line bundles on $X \times_R \operatorname{Spec} R[\epsilon]$ trivial after reduction modulo $\epsilon$ an element of $H^1$ of the structure sheaf sections of the base-changed cover over $R$, and `hδ` states that $\delta$ is a deformation-class map: whenever frames $e_0, e_1$ of the bundle on the two opens and $f$ in the overlap ring satisfy $e_1 = (1 + \epsilon f) e_0$ on the overlap, $\delta$ of the class is the class of $f$. The $R$-linear equivalence $j$ identifies that $H^1$ with $H^1$ of the structure sheaf sections of $\mathcal{V}$ itself, its inverse being the base-change map `H1baseChangeMap 𝒱 c R` (`hj`). The ring homomorphism $\iota : A_0 \to$ `modularFunctionFieldBar p` is compatible with the structure maps from $R$ through $\overline{\mathbf{Q}}$ (`hιR`); `hgen0` says the generic point of $M_0.C$ lies in the preimage of $U_0$ under $e_0$ followed by the projection to $X$; and `hιdef` identifies $\iota$ with $q$-expansion: for every $a \in A_0$, the Laurent series underlying $\iota(a)$ is the coefficientwise image under $\mathbf{Q} \to \overline{\mathbf{Q}}$ of the Laurent series underlying the element of `modularFunctionFieldFull p` obtained from $a$ by pulling back along $e_0$ followed by the projection to $X$, taking the germ at the generic point of $M_0.C$ and applying `M₀.ffEquiv.symm`. Finally $res$ is an additive map from $H^0$ of the Kähler sections to $\Omega_{\mathrm{modularFunctionFieldBar}\,p / \overline{\mathbf{Q}}}$ which, by `hres`, sends $\omega$ to the image of its $U_0$-component $\omega.\mathrm{val}.1 \in \Omega_{A_0/R}$ under the map on Kähler differentials induced by $R \to \overline{\mathbf{Q}}$ and $\iota$.
--
--   **Conclusion.** For all $\omega, \omega'$ in $H^0$ of the Kähler sections of $\mathcal{V}$ over $c$ such that
--   $$res(\omega') = \mathrm{heckeDiffBar}\,p\,q\,(res(\omega)),$$
--   where `heckeDiffBar p q` is the endomorphism of $\Omega_{\mathrm{modularFunctionFieldBar}\,p / \overline{\mathbf{Q}}}$ attached by the correspondence construction to the pair of degeneracy embeddings `heckeBetaBar` and `heckeAlphaBar` at level $p$ and index $q$, and for all $x, x'$ in the set of points of $D$ with values in $\operatorname{Spec} R[\epsilon]$ over $\operatorname{Spec}$ of $R \to R[\epsilon]$ whose composition with the reduction $\operatorname{Spec} R \to \operatorname{Spec} R[\epsilon]$ (induced by $R[\epsilon] \to R$) is the identity element of the relative group law over $\operatorname{Spec}$ of the identity map of $R$: if $x'$ is $x$ followed by $\varphi_1$, then
--   $$\langle \omega,\ j(\delta(h.\mathrm{kerPointsToRigKer}\,R\,x')) \rangle = \langle \omega',\ j(\delta(h.\mathrm{kerPointsToRigKer}\,R\,x)) \rangle,$$
--   both sides being values of the integral Serre pairing `serrePairingInt Λ hv` in $R$, and `kerPointsToRigKer` sending such a point to the class of the pullback of the Poincaré bundle along it.
--
--   This is the adjunction, for the integral Serre pairing computed in sectional Laurent charts on a smooth proper $\mathbf{Z}_{(\ell)}$-model whose generic fibre carries the level-$p$ modular function field, between the Hecke operator at $q$ acting on differentials and the induced endomorphism $\varphi_1$ of the relative $\operatorname{Pic}^0$ on deformation classes of dual-number points: pairing a differential with the $\varphi_1$-translate of a class equals pairing its Hecke image with the class. It is used in the identification of the dual-number kernel points of the relative Jacobian with integral additive maps on the Hecke-stable lattice of differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_serrePairingInt_deformationClass_heckeGen_eq_of_isCompletionAlong_of_res_eq_heckeDiffBar.lean

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
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverSectional
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian ModularCurve AlgebraicCurve IsLocalRing CuspForm Scheme.TwoAffineOpenCover

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.serrePairingInt_deformationClass_heckeGen_eq_of_isCompletionAlong_of_res_eq_heckeDiffBar
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

    (φ₁ : SchemeHomOver D.toBase D.toBase)
    (hφ₁ :
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
          (x y : SchemeHomOver s D.toBase),
        NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s x y) φ₁ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s (NeronModelInfra.schemeHomOverComp x φ₁)
            (NeronModelInfra.schemeHomOverComp y φ₁)))
    (hmoduli :
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of ℚ))
          (M : RigidifiedLineBundle c ε (t' ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))
          (hM : (algEquivZeroCut c ε).P (t' ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ) M),
        Nonempty ((h.poincare.pullbackAlong
            (NeronModelInfra.schemeHomOverComp (h.classify (t' ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ) M hM) φ₁)).L ≅
          Scheme.Modules.rigidify (rigSection c (t' ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ) ε) (pullback.snd c (t' ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))
            (Scheme.Modules.normModule (curveChange πα Hα (t' ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)) d
              ((Scheme.Modules.pullback (curveChange πβ Hβ (t' ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))).obj M.L)))))

    (𝒱 : X.TwoAffineOpenCover) {ιT : Type} [Fintype ιT] (Λ : ιT → (𝒱.cover c).LaurentChart)
    (hv : (𝒱.cover c).ResiduesVanishOnCoboundaries Λ)

    (σ : ιT → (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)) ⟶ X)) (hσ : 𝒱.IsSectional c σ)
    (hΛ : ∀ i, (Λ i).IsCompletionAlong (𝒱.cover c).ρ0
      (Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (hσ.comp_eq i) (hσ.range_subset i)))
    (hΛt : ∀ i, (Λ i).HasParameter (𝒱.cover c).ρ0)

    {δ : RigKerDualNumber c ε ↥(GaloisRep.ratLocalizedAt ℓ) → H1StructureSheaf c ↥(GaloisRep.ratLocalizedAt ℓ) 𝒱}
    (hδ : IsDeformationClassMap c ε ↥(GaloisRep.ratLocalizedAt ℓ) 𝒱 δ)
    (j : H1StructureSheaf c ↥(GaloisRep.ratLocalizedAt ℓ) 𝒱 ≃ₗ[↥(GaloisRep.ratLocalizedAt ℓ)] (𝒱.structureSheafSections c).H1)
    (hj : ∀ y, j.symm y = Scheme.TwoAffineOpenCover.H1baseChangeMap 𝒱 c ↥(GaloisRep.ratLocalizedAt ℓ) y)

    (ι : (𝒱.cover c).A0 →+* ↥(modularFunctionFieldBar p))
    (hιR : ι.comp (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (𝒱.cover c).A0) =
      (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))
    (hgen0 : genericPoint M₀.C ∈ (e₀ ≫ pullback.fst c _) ⁻¹ᵁ 𝒱.U0)
    (hιdef : ∀ a : (𝒱.cover c).A0, ((ι a : ↥(modularFunctionFieldBar p)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (((M₀.ffEquiv.symm ((M₀.C.presheaf.germ ((e₀ ≫ pullback.fst c _) ⁻¹ᵁ 𝒱.U0) (genericPoint M₀.C) hgen0).hom (((e₀ ≫ pullback.fst c _).app (𝒱.U0)).hom a))) : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))
    (res : ↥((𝒱.kaehlerSections c).H0) →+ Ω[modularFunctionFieldBar p⁄AlgebraicClosure ℚ])
    (hres : ∀ ω : ↥((𝒱.kaehlerSections c).H0),
      res ω = KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)) ι hιR ω.val.1) :
    ∀ (ω ω' : ↥((𝒱.kaehlerSections c).H0)), res ω' = heckeDiffBar p q (res ω) →
      ∀ (x x' : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (DualNumber ↥(GaloisRep.ratLocalizedAt ℓ))))) D.toBase //
          Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom ↥(GaloisRep.ratLocalizedAt ℓ) ↥(GaloisRep.ratLocalizedAt ℓ) ↥(GaloisRep.ratLocalizedAt ℓ)).toRingHom) ≫ x.1 =
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(GaloisRep.ratLocalizedAt ℓ))))).1}),
        x'.1.1 = x.1.1 ≫ φ₁.1 →
          (𝒱.cover c).serrePairingInt Λ hv ω (j (δ (h.kerPointsToRigKer ↥(GaloisRep.ratLocalizedAt ℓ) x'))) =
            (𝒱.cover c).serrePairingInt Λ hv ω' (j (δ (h.kerPointsToRigKer ↥(GaloisRep.ratLocalizedAt ℓ) x))) := by sorry
