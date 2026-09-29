-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_hom_classifies_norm_pullback_poincare_heckeDegeneracyPair_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_hom_classifies_norm_pullback_poincare_heckeDegeneracyPair_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/4e4c621d-a510-597a-a340-947f4439b329
-- title:
--   Hecke endomorphism T_ℓ of the relative Pic⁰ of X₁(Mp)
-- statement:
--   Arithmetic data. Let $p$ be a prime and $M$ a nonzero natural number with $5 \le M$ and $p \nmid M$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $p$, and let $\zeta \in L$ be a primitive $p$-th root of unity. Let $K$ be an intermediate field of $L \subseteq L((q))$ (the Laurent series field `LaurentSeries L`) which, by the hypothesis `hK`, equals [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103): the subfield of $L((q))$ generated over $L$ by the image of the intermediate field [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137) of $\mathbb{Q} \subseteq \mathbb{Q}((q))$ under the coefficientwise embedding [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) induced by $\mathbb{Q} \to L$. Let $A$ be a discrete valuation domain with fraction field $L$, with $p$ in the maximal ideal of $A$ (hypothesis `hAp`) and with $\zeta$ in the image of $A \to L$ (hypothesis `hζA`), and let $K$ be an $A$-algebra in a scalar tower over $L$. Let $j \in K$ be nonzero with image [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81) in $L((q))$, the $q$-expansion of the $j$-invariant.
--
--   Write $X =$ [`ModularCurve.TwoChartModel A ↥K j`](def/ModularCurve_TwoChartModel.html#L229), the scheme obtained by glueing the spectra of the subalgebras [`ModularCurve.TwoChart.chartAlgFin A (↥K) j`](def/ModularCurve_TwoChartModel.html#L135) (the elements of $K$ integral over $A[j]$) and [`ModularCurve.TwoChart.chartAlgInf A (↥K) j`](def/ModularCurve_TwoChartModel.html#L137) (those integral over $A[j^{-1}]$) along their common chart, and let $c =$ [`ModularCurve.TwoChart.modelTo A (↥K) j`](def/ModularCurve_TwoChartModel.html#L252) be its structure morphism to $\operatorname{Spec} A$; $c$ is assumed proper.
--
--   Picard datum. Let $\varepsilon$ be a section of $c$, that is a morphism $\operatorname{Spec} A \to X$ with $\varepsilon \cdot c = \mathrm{id}$. Let $D$ be a `RelativePic0Designation` for $c$: a scheme $D.P$ together with a morphism $D.\mathrm{toBase} : D.P \to \operatorname{Spec} A$ and a section $D.\mathrm{zeroSection}$ of it. The hypothesis `hrep` asserts that the type `RepresentsRelSubPic c ε (algEquivZeroCut c ε) D` is nonempty, i.e. that there is a rigidified line bundle $\mathcal{P}$ (the Poincaré bundle) on $X \times_{\operatorname{Spec} A} D.P$, trivialised along the section $\mathrm{rigSection}$ determined by $\varepsilon$, whose geometric fibres over points of $D.P$ are algebraically equivalent to zero, and which is universal for that condition: every rigidified line bundle over a base $t : T \to \operatorname{Spec} A$ with fibrewise algebraically trivial restrictions is, up to isomorphism, the pullback of $\mathcal{P}$ along a unique morphism $T \to D.P$ over $\operatorname{Spec} A$, the pullback along $D.\mathrm{zeroSection}$ being trivial. Further, $D.\mathrm{toBase}$ is smooth (`hsm`) and separated (`hsep`).
--
--   Conditions over the generic point. The base change of $c$ along $A \to L$ is smooth of relative dimension $1$ (`hsmL`) and geometrically integral (`hgiL`); the base change `pullback.snd D.toBase (specMap A L)` of $D.\mathrm{toBase}$ along $A \to L$ is proper (`hprL`) and geometrically connected (`hgcL`).
--
--   Condition on the other fibres (`hsf`). For every algebraically closed field $k$ and every ring homomorphism $f : A \to k$ with nonzero kernel, the fibre $X \times_{\operatorname{Spec} A} \operatorname{Spec} k$ is reduced and there exist two proper smooth geometrically integral curves $C_1, C_2$ over $k$, each equipped with a cover by two affine opens, together with closed immersions $i_1, i_2$ of $C_1, C_2$ into that fibre over $k$, such that every point of the fibre lies in the image of $i_1$ or of $i_2$, and such that the scheme-theoretic intersection `pullback i₁.1 i₂.1` is reduced with exactly $n$ points for some $n > 0$.
--
--   Hecke degeneracy data. Let $\ell$ be a prime. Put $K_\ell =$ [`ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))`](def/ModularCurve_LaurentCoeff.html#L103), the subfield of $L((q))$ generated over $L$ by the image under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of the $q$-expansion field of $\Gamma_1(Mp) \cap \Gamma_0(Mp\ell)$ over $\mathbb{Q}$; it is an $A$-algebra in a scalar tower over $L$. Let $j_\ell \in K_\ell$ be nonzero with image [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81) in $L((q))$, and write $X_\ell =$ [`ModularCurve.TwoChartModel A ↥K_ℓ jℓ`](def/ModularCurve_TwoChartModel.html#L229) with structure morphism $c_\ell =$ [`ModularCurve.TwoChart.modelTo A (↥K_ℓ) jℓ`](def/ModularCurve_TwoChartModel.html#L252). Let $\pi_\alpha, \pi_\beta : X_\ell \to X$ be morphisms over $\operatorname{Spec} A$ (elements of `SchemeHomOver c_ℓ c`), both finite and locally of finite presentation, and surjective on underlying points (`hsurjα`, `hsurjβ`). Let $\iota_\alpha, \iota_\beta$ be $A$-algebra homomorphisms from [`ModularCurve.TwoChart.chartAlgFin A (↥K) j`](def/ModularCurve_TwoChartModel.html#L135) to [`ModularCurve.TwoChart.chartAlgFin A (↥K_ℓ) jℓ`](def/ModularCurve_TwoChartModel.html#L135) such that for every $b$ in the source the Laurent series of $\iota_\alpha b$ equals that of $b$ (`hια`), while the Laurent series of $\iota_\beta b$ equals [`ModularCurve.qExpand L ℓ`](def/ModularCurve_X0.html#L25) applied to that of $b$ (`hιβ`), the substitution multiplying exponents by $\ell$. The hypotheses `hsqα`, `hsqβ` require the squares with the finite-chart inclusions to commute: [`ModularCurve.TwoChart.ιFin A (↥K_ℓ) jℓ`](def/ModularCurve_TwoChartModel.html#L231) followed by $\pi_\alpha$ (resp. $\pi_\beta$) equals $\operatorname{Spec}$ of $\iota_\alpha$ (resp. $\iota_\beta$) followed by [`ModularCurve.TwoChart.ιFin A (↥K) j`](def/ModularCurve_TwoChartModel.html#L231); the hypotheses `hpreα`, `hpreβ` require the preimage under $\pi_\alpha$ (resp. $\pi_\beta$) of the open range of the finite-chart inclusion of $X$ to be the open range of the finite-chart inclusion of $X_\ell$. Finally, let $U$ be an open of $X$ containing every point whose local ring has Krull dimension at most $1$ (`hUdim`), such that the restrictions of $\pi_\alpha$ and of $\pi_\beta$ over $U$ are flat (`hflα`, `hflβ`) and have fibre rank at every point of $U$ equal to $\ell$ if $\ell \mid Mp$ and to $\ell + 1$ otherwise (`hrkα`, `hrkβ`).
--
--   Conclusion. Under these hypotheses there exist a module $\mathcal{N}$ on $X \times_{\operatorname{Spec} A} D.P$ and a morphism $T_\ell : D.P \to D.P$ over $\operatorname{Spec} A$ (an element of `SchemeHomOver D.toBase D.toBase`) such that the following four assertions hold.
--
--   First, $\mathcal{N}$ is invertible, i.e. locally isomorphic to the unit module.
--
--   Second, for every open $V$ of $X \times_{\operatorname{Spec} A} D.P$ and every natural number $d'$, if the restriction over $V$ of the morphism `curveChange πα.1 πα.2 D.toBase`, that is $\pi_\alpha \times \mathrm{id} : X_\ell \times_{\operatorname{Spec} A} D.P \to X \times_{\operatorname{Spec} A} D.P$, is flat and locally of finite presentation and has fibre rank $d'$ at every point of $V$, then the restriction of $\mathcal{N}$ to $V$ is isomorphic to the norm module `Scheme.Modules.normModule` of that restriction in degree $d'$ applied to the restriction, to the preimage of $V$, of the pullback of the Poincaré bundle $\mathcal{P} =$ `hrep.some.poincare.L` along `curveChange πβ.1 πβ.2 D.toBase`, i.e. along $\pi_\beta \times \mathrm{id}$; here $\mathrm{normModule}(\pi, d, \mathcal{L}) = \det_d(\pi_* \mathcal{L}) \otimes \det_d(\pi_* \mathcal{O})^{\vee}$.
--
--   Third, the line bundle underlying the pullback of the Poincaré bundle along $T_\ell$, namely `(hrep.some.poincare.pullbackAlong Tℓ).L`, is isomorphic to the rigidification `Scheme.Modules.rigidify` of $\mathcal{N}$, that is to $\mathcal{N} \otimes q^{*}\bigl(\sigma^{*}\mathcal{N}\bigr)^{\vee}$, where $\sigma$ is the section `rigSection c D.toBase ε` of the projection $q =$ `pullback.snd c D.toBase` determined by $\varepsilon$.
--
--   Fourth, $T_\ell$ is a homomorphism for the group law on points of $D$ obtained from the representability datum `hrep.some` via `RepresentsRelSubPic.relativeGroupLaw` for the group condition `algEquivZeroGroupCut`: for every scheme $T$, every $s : T \to \operatorname{Spec} A$ and all $x, y \in$ `SchemeHomOver s D.toBase`, the composite of the product $x \cdot y$ with $T_\ell$ equals the product of the composite of $x$ with $T_\ell$ and the composite of $y$ with $T_\ell$.
--
--   Fifth, $T_\ell$ fixes the zero section: $D.\mathrm{zeroSection}$ followed by $T_\ell$ equals $D.\mathrm{zeroSection}$.
--
--   This is the construction, on the object $D$ representing the relative $\mathrm{Pic}^0$ of the two-chart integral model of $X_1(Mp)$ over a discrete valuation ring $A$ with fraction field a cyclotomic field, of the endomorphism induced by the Hecke correspondence at $\ell$: it is characterised by the norm along one degeneracy map of the pullback along the other of the Poincaré bundle, is additive on points and fixes the zero section. It feeds the descent of the Hecke action to the special fibre and the statement that every $T_\ell$ is realised on $D$ compatibly with the Abel–Jacobi map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_hom_classifies_norm_pullback_poincare_heckeDegeneracyPair_twoChartModel_x1_mul.lean

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
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
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

theorem ModularCurve.XOneP.exists_hom_classifies_norm_pullback_poincare_heckeDegeneracyPair_twoChartModel_x1_mul
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

    (hsmL : SmoothOfRelativeDimension 1 (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))
    (hgiL : GeometricallyIntegral (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))
    (hprL : IsProper (pullback.snd D.toBase (specMap A L)))
    (hgcL : GeometricallyConnected (pullback.snd D.toBase (specMap A L)))

    (hsf : ∀ (k : Type) [Field k] [IsAlgClosed k] (f : A →+* k), RingHom.ker f ≠ ⊥ →
      ∃ (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
        (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
        (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
        (i₁ : SchemeHomOver c₁ (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom f))))
        (i₂ : SchemeHomOver c₂ (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom f))))
        (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ)
        (_ : C₁.TwoAffineOpenCover) (_ : C₂.TwoAffineOpenCover),
        IsReduced (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom f))) ∧
        (∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom f))), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n)

    (ℓ : ℕ) [Fact ℓ.Prime]

    [Algebra A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))]
    [IsScalarTower A L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))]
    (jℓ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))))
    (hjℓ : ((jℓ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (jℓ ≠ 0)]

    (πα πβ : SchemeHomOver (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (ModularCurve.TwoChart.modelTo A (↥K) j))
    [IsFinite πα.1] [IsFinite πβ.1] [LocallyOfFinitePresentation πα.1] [LocallyOfFinitePresentation πβ.1]
    (ια ιβ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →ₐ[A] ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ))
    (U : (ModularCurve.TwoChartModel A (↥K) j).Opens)
    (hsurjα : Function.Surjective πα.1.base) (hsurjβ : Function.Surjective πβ.1.base)
    (hια : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), (((ια b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ)) : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) = ((b : ↥K) : LaurentSeries L))
    (hιβ : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), (((ιβ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ)) : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) =
        ModularCurve.qExpand L ℓ ((b : ↥K) : LaurentSeries L))
    (hsqα : ModularCurve.TwoChart.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ ≫ πα.1 = Spec.map (CommRingCat.ofHom ια.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j)
    (hsqβ : ModularCurve.TwoChart.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ ≫ πβ.1 = Spec.map (CommRingCat.ofHom ιβ.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j)
    (hpreα : πα.1 ⁻¹ᵁ (ModularCurve.TwoChart.ιFin A (↥K) j).opensRange = (ModularCurve.TwoChart.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ).opensRange)
    (hpreβ : πβ.1 ⁻¹ᵁ (ModularCurve.TwoChart.ιFin A (↥K) j).opensRange = (ModularCurve.TwoChart.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ).opensRange)
    (hUdim : ∀ x : ↥(ModularCurve.TwoChartModel A (↥K) j), ringKrullDim ((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk x) ≤ 1 → x ∈ U)
    (hflα : Flat (πα.1 ∣_ U)) (hflβ : Flat (πβ.1 ∣_ U))
    (hrkα : ∀ y : ↥(ModularCurve.TwoChartModel A (↥K) j), y ∈ U → πα.1.finrank y = (if ℓ ∣ M * p then ℓ else ℓ + 1))
    (hrkβ : ∀ y : ↥(ModularCurve.TwoChartModel A (↥K) j), y ∈ U → πβ.1.finrank y = (if ℓ ∣ M * p then ℓ else ℓ + 1))
 :
    ∃ (𝒩 : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) D.toBase).Modules) (Tℓ : SchemeHomOver D.toBase D.toBase),
      Scheme.Modules.IsInvertible 𝒩 ∧
      (∀ (V : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) D.toBase).Opens) (d' : ℕ),
        Flat ((curveChange πα.1 πα.2 D.toBase) ∣_ V) → LocallyOfFinitePresentation ((curveChange πα.1 πα.2 D.toBase) ∣_ V) →
        (∀ y : V, ((curveChange πα.1 πα.2 D.toBase) ∣_ V).finrank y = d') →
        Nonempty ((Scheme.Modules.pullback V.ι).obj 𝒩 ≅
          Scheme.Modules.normModule ((curveChange πα.1 πα.2 D.toBase) ∣_ V) d'
            ((Scheme.Modules.pullback ((curveChange πα.1 πα.2 D.toBase) ⁻¹ᵁ V).ι).obj
              ((Scheme.Modules.pullback (curveChange πβ.1 πβ.2 D.toBase)).obj hrep.some.poincare.L)))) ∧
      Nonempty ((hrep.some.poincare.pullbackAlong Tℓ).L ≅
        Scheme.Modules.rigidify (rigSection (ModularCurve.TwoChart.modelTo A (↥K) j) D.toBase ε) (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) D.toBase) 𝒩) ∧
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x y : SchemeHomOver s D.toBase),
        NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s x y) Tℓ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
            (NeronModelInfra.schemeHomOverComp x Tℓ) (NeronModelInfra.schemeHomOverComp y Tℓ)) ∧
      D.zeroSection ≫ Tℓ.1 = D.zeroSection := by sorry
