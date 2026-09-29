-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_zmodp_models_components_and_pic0_specialFibre_twoChartModel_x1_mul_of_poincare_iso
-- name    : ModularCurve.XOneP.exists_zmodp_models_components_and_pic0_specialFibre_twoChartModel_x1_mul_of_poincare_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/8e267638-8648-529a-a4fa-efa0d0339f4f
-- title:
--   𝔽ₚ-models of special-fibre components and their relative Pic⁰
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $5 \le M$ and $p \nmid M$.
--
--   *Arithmetic data.* $L$ is a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $p$, and $\zeta \in L$ is a primitive $p$-th root of unity. $K$ is an intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$, required by `hK` to be [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), that is the subfield generated over $L$ by the image, under the coefficientwise map [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) induced by $\mathbb{Q} \to L$, of the field [`ModularCurve.x1FunctionFieldC ℚ (M * p)`](def/ModularCurve_X1.html#L134) of $q$-expansions attached to $\Gamma_1(Mp)$. $A$ is a discrete valuation domain with an $A$-algebra structure on $L$ making $L$ the fraction field of $A$, subject to `hAp`, which puts $p$ in the maximal ideal of $A$, and `hζA`, which asserts that $\zeta$ lies in the image of $A$; $K$ is an $A$-algebra compatibly with the tower $A \to L \to K$. Finally $j \in K$ is an element, non-zero, whose image in $\mathrm{LaurentSeries}\,L$ is [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81), the coefficient extension of the $q$-expansion of the modular invariant.
--
--   Throughout, $X \to \operatorname{Spec} A$ denotes [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252), the structure morphism of the two-chart model [`ModularCurve.TwoChartModel A K j`](def/ModularCurve_TwoChartModel.html#L229), the pushout of the spectra of the two chart algebras of $K/A$ attached to $j$ and to $j^{-1}$.
--
--   *Geometric special fibre.* $k$ is an algebraically closed field of characteristic $p$ with an $A$-algebra structure. $C_1 \to \operatorname{Spec} k$ and $C_2 \to \operatorname{Spec} k$, written $c_1, c_2$, are proper, smooth of relative dimension $1$ and geometrically integral; $i_1, i_2$ are morphisms from $C_1$, $C_2$ to the fibre product $X \times_{\operatorname{Spec} A} \operatorname{Spec} k$ compatible with the structure morphisms (that is, whose composites with the second projection are $c_1$, $c_2$), and both underlying morphisms are closed immersions. The hypothesis `hcover` says that every point of $X \times_{\operatorname{Spec} A} \operatorname{Spec} k$ lies in the image of the underlying map of $i_1$ or of $i_2$; `hred` says that the scheme-theoretic intersection `pullback i₁.1 i₂.1` is reduced, and `hn`, `hn0` say that its underlying set has exactly $n$ points with $n > 0$.
--
--   *Sections.* $\varepsilon$ is a section of $X \to \operatorname{Spec} A$, and $\varepsilon_1$, $\varepsilon_2$ are sections of $c_1$, $c_2$; the hypothesis `hε₁` requires that $\varepsilon_1$ followed by $i_1$ be the base-changed section `sectionBaseChange k ε` of $X \times_A k \to \operatorname{Spec} k$.
--
--   *Relative $\mathrm{Pic}^0$ over $A$.* $D$ is a `RelativePic0Designation` for $X \to \operatorname{Spec} A$: a scheme $D.P$ with a structure morphism $D.\mathrm{toBase} \colon D.P \to \operatorname{Spec} A$ and a section of it. The hypothesis `hrep` provides a witness that $D$ represents, relative to $\varepsilon$, the functor of rigidified line bundles satisfying `algEquivZeroCut`: for $t \colon T \to \operatorname{Spec} A$ a rigidified line bundle is an invertible module on $X \times_A T$ together with a trivialisation of its restriction along the section `rigSection`, and the condition imposed is `FibrewiseAlgEquivZero`, namely that for every algebraically closed field and every point of $T$ over it the restriction to the corresponding geometric fibre is algebraically equivalent to zero; a witness consists of a Poincaré object on $X \times_A D.P$ satisfying the condition, the universal property that every such rigidified bundle over $t$ is induced from the Poincaré object along a unique morphism $T \to D.P$ over $\operatorname{Spec} A$, and triviality of the pullback along the zero section. The hypotheses `hsm` and `hsep` say that $D.\mathrm{toBase}$ is smooth and separated. The hypothesis `hreps` is a witness of the same kind for the base change $X \times_A k \to \operatorname{Spec} k$, the section `sectionBaseChange k ε` and the designation `D.baseChange k` (whose underlying scheme is $D.P \times_A k$), and `hPk` asserts the existence of an isomorphism between the Poincaré bundle of `hreps` and the bundle obtained, via `BaseChange.ofR`, from the pullback of the Poincaré bundle of `hrep` along the first projection $D.P \times_A k \to D.P$.
--
--   *Relative $\mathrm{Pic}^0$ of the components.* $D_1$, $D_2$ are `RelativePic0Designation`s for $c_1$, $c_2$ over $k$, with witnesses `hrep₁`, `hrep₂` that they represent the corresponding rigidified functors cut out by `algEquivZeroCut` with respect to $\varepsilon_1$, $\varepsilon_2$.
--
--   *The restriction map to the second component.* $\nu_2$ is a morphism $D.P \times_A k \to D_2.P$ over $\operatorname{Spec} k$, and `hν₂` characterises it on points: for every $t \colon T \to \operatorname{Spec} k$ and every $a \colon T \to D.P \times_A k$ over $t$, the pullback of the Poincaré bundle of `hrep₂` along $a$ followed by $\nu_2$ is isomorphic to the rigidification, along `rigSection c₂ t ε₂` and the projection $C_2 \times_k T \to T$, of the restriction along `curveChange i₂.1 i₂.2 t` of the pullback along $a$ of the Poincaré bundle of `hreps`; here `rigidify σ q L` is $L \otimes q^{*}((\sigma^{*}L)^{\vee})$.
--
--   Finally, $\mathbb{Z}/p$ is an $A$-algebra and $k$ a $\mathbb{Z}/p$-algebra, compatibly with the $A$-algebra structure of $k$.
--
--   *Conclusion.* There exist schemes $C_{1,p}$, $C_{2,p}$ with structure morphisms $c_{1,p}, c_{2,p}$ to $\operatorname{Spec} \mathbb{Z}/p$, morphisms $i_{1,p}, i_{2,p}$ from them to $X \times_A \operatorname{Spec} \mathbb{Z}/p$, morphisms $g_1 \colon C_1 \to C_{1,p}$ and $g_2 \colon C_2 \to C_{2,p}$, designations $D_{1,p}$, $D_{2,p}$ for $c_{1,p}$, $c_{2,p}$ over $\mathbb{Z}/p$, sections $\varepsilon_{1,p}$, $\varepsilon_{2,p}$ of $c_{1,p}$, $c_{2,p}$, witnesses `hrep₁ₚ`, `hrep₂ₚ` that $D_{1,p}$, $D_{2,p}$ represent the `algEquivZeroCut` functors over $\mathbb{Z}/p$ and witnesses `hrep₁ₚk`, `hrep₂ₚk` that `D₁ₚ.baseChange k`, `D₂ₚ.baseChange k` represent the corresponding functors for $C_{i,p} \times_{\mathbb{Z}/p} k$ with the base-changed sections, morphisms $\theta_1 \colon D_1.P \to D_{1,p}.P \times_{\mathbb{Z}/p} k$ and $\theta_2 \colon D_2.P \to D_{2,p}.P \times_{\mathbb{Z}/p} k$ over $\operatorname{Spec} k$, a morphism $\pi_p \colon D.P \times_A k \to D.P \times_A \mathbb{Z}/p$, and morphisms $\nu_{1,p}, \nu_{2,p} \colon D.P \times_A \mathbb{Z}/p \to D_{1,p}.P,\ D_{2,p}.P$ over $\operatorname{Spec} \mathbb{Z}/p$, such that all of the following hold.
--
--   The kernel of $A \to \mathbb{Z}/p$ is the maximal ideal of $A$.
--
--   The squares $(g_1, c_1, c_{1,p}, \operatorname{Spec} k \to \operatorname{Spec} \mathbb{Z}/p)$ and $(g_2, c_2, c_{2,p}, \operatorname{Spec} k \to \operatorname{Spec} \mathbb{Z}/p)$ are pullback squares, so $C_i \cong C_{i,p} \times_{\mathbb{Z}/p} k$ with $g_i$ and $c_i$ the two projections.
--
--   The morphisms $i_{1,p}$ and $i_{2,p}$ are closed immersions, and each followed by the second projection $X \times_A \mathbb{Z}/p \to \operatorname{Spec} \mathbb{Z}/p$ gives $c_{1,p}$, respectively $c_{2,p}$.
--
--   For $i = 1, 2$: $g_i$ followed by $i_{i,p}$ followed by the first projection $X \times_A \mathbb{Z}/p \to X$ equals $i_i$ followed by the first projection $X \times_A k \to X$.
--
--   For $i = 1, 2$: the Poincaré bundle of `hrepᵢₚk` is isomorphic to the bundle obtained, via `BaseChange.ofR`, from the pullback of the Poincaré bundle of `hrepᵢₚ` along the first projection $D_{i,p}.P \times_{\mathbb{Z}/p} k \to D_{i,p}.P$.
--
--   The underlying morphisms of $\theta_1$ and $\theta_2$ are isomorphisms.
--
--   Both $\theta_1$ and $\theta_2$ are homomorphisms for the relative group laws obtained from the representability witnesses with respect to `algEquivZeroGroupCut`: for every $s \colon T \to \operatorname{Spec} k$ and all $x, y \colon T \to D_1.P$ over $s$, the product of $x$ and $y$ followed by $\theta_1$ equals the product of $x$ followed by $\theta_1$ and $y$ followed by $\theta_1$ computed in $D_{1,p}.P \times_{\mathbb{Z}/p} k$, and likewise for $D_2$, $\theta_2$ and $D_{2,p}$.
--
--   The morphism $\pi_p$ is compatible with both projections: $\pi_p$ followed by the first projection $D.P \times_A \mathbb{Z}/p \to D.P$ is the first projection $D.P \times_A k \to D.P$, and $\pi_p$ followed by the second projection to $\operatorname{Spec} \mathbb{Z}/p$ equals the second projection $D.P \times_A k \to \operatorname{Spec} k$ followed by $\operatorname{Spec} k \to \operatorname{Spec} \mathbb{Z}/p$.
--
--   Finally, both restriction maps descend to $\mathbb{Z}/p$: the canonical morphism `RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some` from $D.P \times_A k$ to $D_1.P$ attached to the closed immersion $i_1$, followed by $\theta_1$ and then by the first projection $D_{1,p}.P \times_{\mathbb{Z}/p} k \to D_{1,p}.P$, equals $\pi_p$ followed by $\nu_{1,p}$; and $\nu_2$ followed by $\theta_2$ and then by the first projection $D_{2,p}.P \times_{\mathbb{Z}/p} k \to D_{2,p}.P$ equals $\pi_p$ followed by $\nu_{2,p}$.
--
--   This is the descent statement that the two components of the geometric special fibre of the two-chart model of $X_1(Mp)$ over $A$ (a discrete valuation ring containing $\zeta_p$ with $p$ in its maximal ideal, whose residue field is therefore $\mathbb{F}_p$), together with the representing objects of their relative $\mathrm{Pic}^0$ functors and the two restriction maps from the relative $\mathrm{Pic}^0$ of the model, are already defined over the prime field. It is used in the analysis of the Frobenius action on the special fibre, in [`ModularCurve.XOneP.addEquiv_proj_fst_eq_frob_smul_of_pts_eq_frobenius_comp_of_gaussReading_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.addEquiv_proj_fst_eq_frob_smul_of_pts_eq_frobenius_comp_of_gaussReading_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_zmodp_models_components_and_pic0_specialFibre_twoChartModel_x1_mul_of_poincare_iso.lean

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
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.XOneP.exists_zmodp_models_components_and_pic0_specialFibre_twoChartModel_x1_mul_of_poincare_iso
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)

    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    (hreps : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)) (D.baseChange k))

    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε k
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A k), pullback.condition⟩)).L))
    (D₁ : RelativePic0Designation k c₁) (hrep₁ : Nonempty (RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁))
    (D₂ : RelativePic0Designation k c₂) (hrep₂ : Nonempty (RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂))

    (ν₂ : SchemeHomOver (D.baseChange k).toBase D₂.toBase)
    (hν₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t (D.baseChange k).toBase),
        Nonempty ((hrep₂.some.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hreps.poincare.pullbackAlong a).L)))

    [Algebra A (ZMod p)] [Algebra (ZMod p) k] [IsScalarTower A (ZMod p) k] :
    ∃ (C₁ₚ C₂ₚ : Scheme.{0}) (c₁ₚ : C₁ₚ ⟶ Spec (CommRingCat.of (ZMod p))) (c₂ₚ : C₂ₚ ⟶ Spec (CommRingCat.of (ZMod p)))
      (i₁ₚ : C₁ₚ ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)))
      (i₂ₚ : C₂ₚ ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)))
      (g₁ : C₁ ⟶ C₁ₚ) (g₂ : C₂ ⟶ C₂ₚ)
      (D₁ₚ : RelativePic0Designation (ZMod p) c₁ₚ) (D₂ₚ : RelativePic0Designation (ZMod p) c₂ₚ)
      (ε₁ₚ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ZMod p)))) c₁ₚ) (ε₂ₚ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ZMod p)))) c₂ₚ)
      (hrep₁ₚ : RepresentsRelSubPic c₁ₚ ε₁ₚ (algEquivZeroCut c₁ₚ ε₁ₚ) D₁ₚ)
      (hrep₂ₚ : RepresentsRelSubPic c₂ₚ ε₂ₚ (algEquivZeroCut c₂ₚ ε₂ₚ) D₂ₚ)
      (hrep₁ₚk : RepresentsRelSubPic (baseChange (ZMod p) c₁ₚ k) (sectionBaseChange k ε₁ₚ)
        (algEquivZeroCut (baseChange (ZMod p) c₁ₚ k) (sectionBaseChange k ε₁ₚ)) (D₁ₚ.baseChange k))
      (hrep₂ₚk : RepresentsRelSubPic (baseChange (ZMod p) c₂ₚ k) (sectionBaseChange k ε₂ₚ)
        (algEquivZeroCut (baseChange (ZMod p) c₂ₚ k) (sectionBaseChange k ε₂ₚ)) (D₂ₚ.baseChange k))
      (θ₁ : SchemeHomOver D₁.toBase (D₁ₚ.baseChange k).toBase) (θ₂ : SchemeHomOver D₂.toBase (D₂ₚ.baseChange k).toBase)

      (πₚ : pullback D.toBase (specMap A k) ⟶ pullback D.toBase (specMap A (ZMod p)))
      (ν₁ₚ : SchemeHomOver (D.baseChange (ZMod p)).toBase D₁ₚ.toBase) (ν₂ₚ : SchemeHomOver (D.baseChange (ZMod p)).toBase D₂ₚ.toBase),

      RingHom.ker (algebraMap A (ZMod p)) = IsLocalRing.maximalIdeal A ∧

      IsPullback g₁ c₁ c₁ₚ (specMap (ZMod p) k) ∧ IsPullback g₂ c₂ c₂ₚ (specMap (ZMod p) k) ∧

      IsClosedImmersion i₁ₚ ∧ IsClosedImmersion i₂ₚ ∧
      i₁ₚ ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)) = c₁ₚ ∧
      i₂ₚ ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)) = c₂ₚ ∧

      g₁ ≫ i₁ₚ ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)) = i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ∧
      g₂ ≫ i₂ₚ ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)) = i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ∧

      Nonempty (hrep₁ₚk.poincare.L ≅ (BaseChange.ofR c₁ₚ ε₁ₚ k
        (hrep₁ₚ.poincare.pullbackAlong ⟨pullback.fst D₁ₚ.toBase (specMap (ZMod p) k), pullback.condition⟩)).L) ∧
      Nonempty (hrep₂ₚk.poincare.L ≅ (BaseChange.ofR c₂ₚ ε₂ₚ k
        (hrep₂ₚ.poincare.pullbackAlong ⟨pullback.fst D₂ₚ.toBase (specMap (ZMod p) k), pullback.condition⟩)).L) ∧

      IsIso θ₁.1 ∧ IsIso θ₂.1 ∧
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver s D₁.toBase),
        NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₁.some).mul s x y) θ₁ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₁ₚk).mul s (NeronModelInfra.schemeHomOverComp x θ₁) (NeronModelInfra.schemeHomOverComp y θ₁)) ∧
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver s D₂.toBase),
        NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₂.some).mul s x y) θ₂ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₂ₚk).mul s (NeronModelInfra.schemeHomOverComp x θ₂) (NeronModelInfra.schemeHomOverComp y θ₂)) ∧

      πₚ ≫ pullback.fst D.toBase (specMap A (ZMod p)) = pullback.fst D.toBase (specMap A k) ∧
      πₚ ≫ pullback.snd D.toBase (specMap A (ZMod p)) = pullback.snd D.toBase (specMap A k) ≫ specMap (ZMod p) k ∧
      (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some).1 ≫ θ₁.1 ≫ pullback.fst D₁ₚ.toBase (specMap (ZMod p) k) = πₚ ≫ ν₁ₚ.1 ∧
      ν₂.1 ≫ θ₂.1 ≫ pullback.fst D₂ₚ.toBase (specMap (ZMod p) k) = πₚ ≫ ν₂ₚ.1 := by sorry
