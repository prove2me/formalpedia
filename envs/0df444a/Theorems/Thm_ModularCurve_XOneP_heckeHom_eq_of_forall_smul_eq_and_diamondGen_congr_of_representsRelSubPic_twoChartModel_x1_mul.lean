-- Prove2me | Theorems.Thm_ModularCurve_XOneP_heckeHom_eq_of_forall_smul_eq_and_diamondGen_congr_of_representsRelSubPic_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.heckeHom_eq_of_forall_smul_eq_and_diamondGen_congr_of_representsRelSubPic_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/990a91e2-dbe3-57c1-ba8f-fe492aaf66b7
-- title:
--   Rigidity of Hecke–diamond endomorphisms on the Jacobian model
-- statement:
--   Fix a prime $p$ and $M$ with $5 \le M$ and $p \nmid M$, a field $L$ of characteristic zero that is a $\{p\}$-cyclotomic extension of $\mathbb{Q}$, a primitive $p$-th root of unity $\zeta \in L$, and the intermediate field $K$ of $\mathrm{Laurent}(L)$ equal to the $L$-base change [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103) of the function field $\mathbb{Q}(X_1(Mp))$ realised as an intermediate field of $\mathrm{Laurent}(\mathbb{Q})$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in its maximal ideal and $\zeta$ lies in the image of $A$, with $K$ an $A$-algebra compatibly, and let $j \in K$ be nonzero with Laurent expansion the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157). Let $\varepsilon$ be a section over $\operatorname{Spec} A$ of the two-chart model [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) (the pushout of the spectra of the integral closures of $A[j]$ and $A[j^{-1}]$ in $K$), assumed proper over $A$; let $D$ consist of a scheme $D.P$ with a morphism $D.\mathrm{toBase}$ to $\operatorname{Spec} A$ and a zero-section, and assume $D$ represents, via a Poincaré bundle with the expected universal property and trivialisation along the zero-section, the functor of rigidified line bundles on the model that are fibrewise algebraically equivalent to zero, with $D.\mathrm{toBase}$ smooth and separated. Assume further: $\mathbb{Q}$-algebra maps $A \to \overline{\mathbb{Q}}$, $L \to \overline{\mathbb{Q}}$ forming a tower; the $L$-base change of the model is smooth of relative dimension $1$ and geometrically integral; the $L$-base change of $D.\mathrm{toBase}$ is proper and geometrically connected; a curve model $M\eta$ over $\overline{\mathbb{Q}}$ with function field $\mathbb{Q}(X_1(Mp)) \otimes \overline{\mathbb{Q}}$ together with an isomorphism $e\eta$ onto the $\overline{\mathbb{Q}}$-fibre of the model commuting with the structure morphisms, whose finite chart has a point, which matches $q$-expansions on the finite chart algebra, and which transports the Galois action on $\overline{\mathbb{Q}}$-points to the [`ModularCurve.arithmeticGalois`](def/ModularCurve_ArithmeticGalois.html#L54) action on places; the existence of all Hecke and diamond inputs at level $Mp$ and pairwise commutation of the resulting endomorphisms of $J_1(Mp) = \mathrm{Pic}^0(\overline{\mathbb{Q}}, \mathbb{Q}(X_1(Mp)) \otimes \overline{\mathbb{Q}})$; a multiplicative semiring action of $\mathrm{Gal}(L/\mathbb{Q})$ on $A$ compatible with $A \to L$. Finally let $g_{\mathrm{pts}}$ be a bijection from $J_1(Mp)$ to the $\overline{\mathbb{Q}}$-points of $D.\mathrm{toBase}$ over $\operatorname{Spec} A$, and $\varphi$ a map from the polynomial ring $\mathrm{HeckeAlgOne} = \mathbb{Z}[X_{\ell}, X_{d}]$ (indexed by primes and by natural numbers) to endomorphisms of $D.P$ over $\operatorname{Spec} A$, such that $g_{\mathrm{pts}}(t \cdot x) = \varphi(t) \circ g_{\mathrm{pts}}(x)$ for all $t$ and all $x$, the action being the one attached to the commuting Hecke and diamond operators. Then: (i) two endomorphisms of $D.P$ over $\operatorname{Spec} A$ that agree after precomposition with every $g_{\mathrm{pts}}(x)$ are equal; (ii) if $t$ and $t'$ act identically on $J_1(Mp)$ then $\varphi(t) = \varphi(t')$; (iii) $\varphi(\langle d \rangle)$ depends only on $d$ modulo $Mp$; (iv) for $d, d'$ coprime to $Mp$ one has $\varphi(\langle dd' \rangle) = \varphi(\langle d \rangle) \circ \varphi(\langle d' \rangle)$ on underlying morphisms; and (v) $\varphi(\langle 1 \rangle)$ is the identity of $D.P$.
--
--   This is the rigidity step for the integral model: the $\overline{\mathbb{Q}}$-points dictionary determines endomorphisms of the scheme representing $\mathrm{Pic}^0$ of the two-chart model of $X_1(Mp)$ over the ring of integers of $\mathbb{Q}(\zeta_p)$, and it transfers the group-theoretic relations satisfied by the diamond operators on $J_1(Mp)$ to relations between the corresponding $A$-endomorphisms. It is used in the subsequent analysis of the special fibre and of the Galois action on the model, in particular in the statements identifying the image of the diamond endomorphisms on the toric part of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_heckeHom_eq_of_forall_smul_eq_and_diamondGen_congr_of_representsRelSubPic_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.heckeHom_eq_of_forall_smul_eq_and_diamondGen_congr_of_representsRelSubPic_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (hsmL : SmoothOfRelativeDimension 1 (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))
    (hgiL : GeometricallyIntegral (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))

    (hprL : IsProper (pullback.snd D.toBase (specMap A L)))
    (hgcL : GeometricallyConnected (pullback.snd D.toBase (specMap A L)))

    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
    (eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase)

    [Mη_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hMηpin : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      ((Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((a : ↥K) : LaurentSeries L))

    (hgal : ∀ (g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)),
      (∀ l : L, g (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
      ∀ (x x' : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // s ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
        Spec.map (CommRingCat.ofHom (g : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ x.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) →
      Mη.pointEquivPlace x' =
        ModularCurve.arithmeticGalois (L := (AlgebraicClosure ℚ)) (ModularCurve.x1FunctionField (M * p)) g • Mη.pointEquivPlace x)
    (hin : ModularCurve.HeckeDiamondInputsAll (M * p)) (hcomm : ModularCurve.HeckeDiamondCommuteBar (M * p))

    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a))

    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (φ : ModularCurve.HeckeAlgOne → SchemeHomOver D.toBase D.toBase)
    (hφpts : letI := ModularCurve.heckeModuleOneBar (M * p)
      ∀ (t : ModularCurve.HeckeAlgOne) (x : ModularCurve.JOne (M * p)), (gpts (t • x)).1 = (gpts x).1 ≫ (φ t).1) :
    letI := ModularCurve.heckeModuleOneBar (M * p)

    (∀ ψ ψ' : SchemeHomOver D.toBase D.toBase,
      (∀ x : ModularCurve.JOne (M * p), (gpts x).1 ≫ ψ.1 = (gpts x).1 ≫ ψ'.1) → ψ = ψ') ∧

    (∀ t t' : ModularCurve.HeckeAlgOne, (∀ x : ModularCurve.JOne (M * p), t • x = t' • x) → φ t = φ t') ∧

    (∀ d d' : ℕ, d ≡ d' [MOD M * p] → φ (ModularCurve.diamondGen d) = φ (ModularCurve.diamondGen d')) ∧

    (∀ d d' : ℕ, d.Coprime (M * p) → d'.Coprime (M * p) →
      (φ (ModularCurve.diamondGen (d * d'))).1 = (φ (ModularCurve.diamondGen d')).1 ≫ (φ (ModularCurve.diamondGen d)).1) ∧

    (φ (ModularCurve.diamondGen 1)).1 = 𝟙 D.P := by sorry
