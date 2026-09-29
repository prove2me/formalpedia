-- Prove2me | Theorems.Thm_ModularCurve_XOneP_mul_comp_galoisHom_eq_mul_comp_of_pts_smul_eq_comp_abelJacobi_of_representsRelSubPic_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.mul_comp_galoisHom_eq_mul_comp_of_pts_smul_eq_comp_abelJacobi_of_representsRelSubPic_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/2f7c5c3b-9085-5c7d-b98f-375d7eb41936
-- title:
--   Galois twists respect the relative group law on D
-- statement:
--   Fix a prime $p$, an $M$ with $5 \le M$ and $p \nmid M$, a field $L$ of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$ together with a primitive $p$-th root of unity $\zeta \in L$, and the intermediate field $K$ of $\mathrm{LaurentSeries}\,L$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), the $L$-base change of the function field of $X_1(Mp)$. Let $A$ be a discrete valuation ring which is a domain with fraction field $L$, with $p$ in its maximal ideal and $\zeta$ in the image of $A$, and let $j \in K$ be the element whose Laurent expansion is [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81) and which is assumed nonzero. Write $c$ for the two-chart model [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) over $\operatorname{Spec} A$, assumed proper, $\varepsilon$ for a section of $c$, and $D$ for a relative $\mathrm{Pic}^0$ designation for $c$ (a scheme $D.P$ with a structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec} A$ and a zero section); `hrep` provides a representation of the relative sub-Picard functor of rigidified line bundles on $c$ satisfying the fibrewise-algebraic-equivalence-to-zero condition `algEquivZeroCut` by $D$, and $D.\mathrm{toBase}$ is assumed smooth and separated. Further hypotheses, summarised here, comprise: compatible $A$- and $L$-algebra structures on $\overline{\mathbb{Q}}$; smoothness of relative dimension $1$ and geometric integrality of the base change of $c$ to $L$; properness and geometric connectedness of the base change of $D.\mathrm{toBase}$ to $L$; a curve model $M\eta$ over $\overline{\mathbb{Q}}$ with function field [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) identified by an isomorphism $e\eta$ with the geometric fibre of $c$, compatibly with the structure morphisms, together with the non-emptiness of the finite chart pulled back along $e\eta$ followed by the first projection, and the requirement that the elements of the chart algebra [`ModularCurve.TwoChart.chartAlgFin A K j`](def/ModularCurve_TwoChartModel.html#L135) have the expected Laurent expansions in $M\eta$'s function field; the assertion `hgal` that a $\mathbb{Q}$-automorphism $g$ of $\overline{\mathbb{Q}}$ fixing $L$ pointwise moves places according to [`ModularCurve.arithmeticGalois`](def/ModularCurve_ArithmeticGalois.html#L54) whenever it moves the corresponding $\overline{\mathbb{Q}}$-points of $M\eta$; the predicates [`ModularCurve.HeckeDiamondInputsAll (M * p)`](def/ModularCurve_X1HeckeModule.html#L58) and [`ModularCurve.HeckeDiamondCommuteBar (M * p)`](def/ModularCurve_X1HeckeModule.html#L54); a multiplicative semiring action of $L \simeq_{\mathbb{Q}} L$ on $A$ compatible with $A \to L$; a bijection $\mathrm{gpts}$ from [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186) (the degree-zero divisor class group of the geometric function field) to the $\overline{\mathbb{Q}}$-points of $D.\mathrm{toBase}$ which is additive for the relative group law attached to `hrep.some`; and, for each $s \in L \simeq_{\mathbb{Q}} L$, a morphism $\tau_s$ of $D.P$ over $\operatorname{Spec}$ of the ring map induced by $s$ on $A$, compatible via `hτpts` with the Galois action on [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186) under $\mathrm{gpts}$. The conclusion asserts that each $\tau_s$ is a homomorphism for the relative group law $m$ obtained from `hrep.some` via `algEquivZeroGroupCut`: for every $s$, every scheme $T$ with a morphism $u : T \to \operatorname{Spec} A$ and all $u$-points $x, y$ of $D.\mathrm{toBase}$, the morphism $m_u(x,y)$ followed by $\tau_s$ equals the product, taken for the twisted base morphism $u$ followed by $\operatorname{Spec}$ of the ring map of $s$, of $x$ followed by $\tau_s$ and $y$ followed by $\tau_s$.
--
--   This is the semilinearity of the Galois twists $\tau_s$ with respect to the group law on the relative $\mathrm{Pic}^0$ model of $X_1(Mp)$ over the valuation ring $A$ of $\mathbb{Q}(\zeta_p)$: the twists are homomorphisms of group laws, not merely maps of schemes. It feeds the construction of the Néron special fibre data for $J_1(Mp)$ in the good-reduction analysis of the modular Jacobian, being cited by [`ModularCurve.XOneP.exists_neronSpecialFibreOpsV3_of_heckeHom_galoisHom_of_representsRelSubPic_of_isAlgebraic_twoChartModel_x1_mul_of_baseChangeIso_of_abelJacobi_of_gaussReading`](thm.html#ModularCurve.XOneP.exists_neronSpecialFibreOpsV3_of_heckeHom_galoisHom_of_representsRelSubPic_of_isAlgebraic_twoChartModel_x1_mul_of_baseChangeIso_of_abelJacobi_of_gaussReading).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_mul_comp_galoisHom_eq_mul_comp_of_pts_smul_eq_comp_abelJacobi_of_representsRelSubPic_twoChartModel_x1_mul.lean

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

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.mul_comp_galoisHom_eq_mul_comp_of_pts_smul_eq_comp_abelJacobi_of_representsRelSubPic_twoChartModel_x1_mul
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
    (τ : ∀ s : L ≃ₐ[ℚ] L,
      SchemeHomOver (D.toBase ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s))) D.toBase)
    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))
    (hτpts : ∀ (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (s : L ≃ₐ[ℚ] L),
      (∀ l : L, σ' (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) (s l)) →
      ∀ x : ModularCurve.JOne (M * p),
        (gpts (σ' • x)).1 = Spec.map (CommRingCat.ofHom σ'.toRingEquiv.toRingHom) ≫ (gpts x).1 ≫ (τ s⁻¹).1) :
    ∀ (s : L ≃ₐ[ℚ] L) {T : Scheme.{0}} (u : T ⟶ Spec (CommRingCat.of A)) (x y : SchemeHomOver u D.toBase),
      ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul u x y).1 ≫ (τ s).1 =
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul
          (u ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)))
          ⟨x.1 ≫ (τ s).1, by rw [Category.assoc, (τ s).2, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ (τ s).1, by rw [Category.assoc, (τ s).2, ← Category.assoc, y.2]⟩).1 := by sorry
