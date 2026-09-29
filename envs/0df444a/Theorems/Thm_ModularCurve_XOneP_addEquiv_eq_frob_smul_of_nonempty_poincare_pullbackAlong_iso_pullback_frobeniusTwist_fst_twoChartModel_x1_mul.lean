-- Prove2me | Theorems.Thm_ModularCurve_XOneP_addEquiv_eq_frob_smul_of_nonempty_poincare_pullbackAlong_iso_pullback_frobeniusTwist_fst_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.addEquiv_eq_frob_smul_of_nonempty_poincare_pullbackAlong_iso_pullback_frobeniusTwist_fst_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/046588d7-8585-5cd2-8b98-7340aedf317b
-- title:
--   Frobenius pull-back acts as coefficientwise Frobenius on the Igusa component
-- statement:
--   Fix a prime $p$ and an integer $M \ge 5$ with $p \nmid M$ (`hM`, `hpM`). Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, let $\zeta \in L$ be a primitive $p$-th root of unity, and let $K$ be the intermediate field of the Laurent series field $L(\!(q)\!)$ over $L$ given by `hK` as $K =$ [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), the subfield generated over $L$ by the coefficientwise image of the function field of $X_1(Mp)$ over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ (`hAp`) and $\zeta$ lies in the image of $A$ (`hζA`), with $K$ an $A$-algebra compatibly with $L$, and let $j \in K$ be the element whose Laurent expansion is the coefficientwise image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular invariant (`hj`), assumed nonzero. Write $X =$ [`ModularCurve.TwoChart.modelTo A ↥K j`](def/ModularCurve_TwoChartModel.html#L252) for the resulting two-chart model over $\operatorname{Spec} A$.
--
--   Let $k$ be an algebraically closed field of characteristic $p$ which is an $A$-algebra, and let $c_1 : C_1 \to \operatorname{Spec} k$ and $c_2 : C_2 \to \operatorname{Spec} k$ be proper, smooth of relative dimension $1$ and geometrically integral. The data $i_1, i_2$ are closed immersions of $C_1$, $C_2$ over the base change `baseChange A X k` of the two-chart model to $k$, with: `hcover`, every point of that base change lies in the image of $i_1$ or of $i_2$; `hred`, the scheme-theoretic intersection `pullback i₁.1 i₂.1` is reduced; and `hn`, `hn0`, its cardinality equals $n > 0$.
--
--   Sections: $\varepsilon$ is a section of $X$ over $\operatorname{Spec} A$, and $\varepsilon_1$, $\varepsilon_2$ are $k$-points of $C_1$, $C_2$ over the identity, with `hε₁` asserting that $\varepsilon_1$ followed by $i_1$ is the base-changed section `sectionBaseChange k ε`.
--
--   Relative Picard data. A `RelativePic0Designation` consists of a scheme together with a structure morphism to the base and a section of it. Here $D$ is such a designation for $X$ over $A$; `hrep` asserts that the relative sub-Picard functor cut out by `algEquivZeroCut` (the condition that a rigidified line bundle be fibrewise algebraically equivalent to zero on all geometric fibres) is represented by $D$, in the sense of `RepresentsRelSubPic`: a Poincaré rigidified bundle on $D$ satisfying the condition, a unique-classification property for every rigidified bundle satisfying it, and triviality along the zero section. The hypotheses `hsm`, `hsep` require `D.toBase` to be smooth and separated. The hypothesis `hreps` is the corresponding representability statement over $k$ for `baseChange A X k` with section `sectionBaseChange k ε` and designation `D.baseChange k`, and `hPk` asserts that its Poincaré bundle is isomorphic to the one obtained from `hrep.some` by pulling back along the first projection of $D$'s base change and applying `BaseChange.ofR`. Similarly $D_1$, $D_2$ are designations for $c_1$, $c_2$ over $k$, with representability hypotheses `hrep₁`, `hrep₂`.
--
--   The morphism $\nu_2$ is a morphism from `(D.baseChange k).toBase` to `D₂.toBase` over $\operatorname{Spec} k$, and `hν₂` requires it to be compatible with the Poincaré bundles: for every $t : T \to \operatorname{Spec} k$ and every $a$ over $t$ with values in `(D.baseChange k).toBase`, the pull-back of the Poincaré bundle of `hrep₂.some` along $a$ followed by $\nu_2$ is isomorphic to the rigidification, along the section `rigSection c₂ t ε₂` and the projection `pullback.snd c₂ t`, of the pull-back along `curveChange i₂.1 i₂.2 t` of the pull-back of the Poincaré bundle of `hreps` along $a$.
--
--   Group-theoretic data. $G$ is a [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9): abelian groups $J_{0s}$, $J_I$, $J_E$, a subgroup `torus` of $J_{0s}$, and a surjective homomorphism `proj` $: J_{0s} \to J_I \times J_E$ with kernel `torus`. The bijections `pts`, `ptsI`, `ptsE` identify $J_{0s}$, $J_I$, $J_E$ with the $k$-points of `(D.baseChange k).toBase`, `D₁.toBase`, `D₂.toBase` respectively. The hypotheses `hadd`, `haddI`, `haddE` assert that each of these dictionaries is additive through the Poincaré bundles: the pull-back along the point attached to a sum is isomorphic to the tensor product of the two pull-backs. The hypothesis `hproj` asserts, for each $x \in J_{0s}$, that `ptsI (G.proj x).1` is `pts x` followed by the classifying morphism `RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some`, and that `ptsE (G.proj x).2` is `pts x` followed by $\nu_2$.
--
--   Igusa data for the component $C_1$. Here $w$ is a [`ModularCurve.IntegralWeightOneForm k M`](def/ModularCurve_IgusaFunctionFieldX1.html#L16), that is, a weight one modular form on $\Gamma_1(M)$ together with an integral $q$-expansion whose reduction over $k$ has nonvanishing constant datum; [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35) is the associated Igusa function field inside $k(\!(q)\!)$. Then $\mathrm{Mdl}_1$ is a `CurveModel` for that field over $k$ (a proper smooth integral curve with an isomorphism of its function field with the given field, together with a bijection between closed points and places compatible with valuation rings), $e_1 : \mathrm{Mdl}_1.C \cong C_1$ is an isomorphism, and `he₁` says that $e_1$ followed by $c_1$ is the structure morphism of $\mathrm{Mdl}_1$. The hypothesis `hne₁` requires the preimage, under $e_1$ followed by $i_1$ followed by the first projection of `baseChange A X k`, of the image of the finite chart [`ModularCurve.TwoChart.ιFin A ↥K j`](def/ModularCurve_TwoChartModel.html#L231) to be nonempty. The Gauss reading `hgauss₁` states: for every $a$ in the finite chart algebra [`ModularCurve.TwoChart.chartAlgFin A ↥K j`](def/ModularCurve_TwoChartModel.html#L135) and all power series $x, y$ over $A$ with $y$ having nonzero reduction over $k$, if $a \cdot y = x$ holds in $L(\!(q)\!)$ after mapping coefficients to $L$, then the Laurent series over $k$ of the element of the Igusa field obtained by transporting, through $\mathrm{Mdl}_1.\mathrm{ffEquiv}^{-1}$, the germ at the generic point of the pull-back of $a$ along $e_1$ followed by $i_1$ followed by the first projection, equals the quotient of the reductions of $x$ and $y$ over $k$.
--
--   Abel–Jacobi dictionary. $\theta_1$ is an isomorphism of additive groups from $J_I$ onto $\operatorname{Pic}^0$ of the Igusa function field over $k$ (degree-zero divisors modulo principal ones, in the sense of places of the field). The hypothesis `hθpin₁` pins it down: for $g \in J_I$ and a $k$-point $x$ of $C_1$, if the pull-back of the Poincaré bundle of `hrep₁.some` along `ptsI g` is isomorphic to the line bundle of the relative effective Cartier divisor `RelEffCartierDiv.ofPoint c₁ x` tensored with the ideal module of `RelEffCartierDiv.ofPoint c₁ ε₁`, then there is a degree-zero divisor $D_v$ equal to the difference of the single divisors at the places `Mdl₁.pointEquivPlace` of $x$ and of $\varepsilon_1$ (each transported through $e_1^{-1}$) with coefficient $1$, and $\theta_1 g =$ `Pic0.mk` $D_v$.
--
--   Frobenius data. `frobIg` is an element of `SemilinearAut k` of the Igusa field, that is, a pair consisting of a ring automorphism of the field and one of $k$ intertwined by the structure map, and `hfrobIg` requires that for every element $x$ of the Igusa field and every $n \in \mathbb{Z}$ the $n$-th Laurent coefficient of `frobIg • x` is the $p$-th power of the $n$-th coefficient of $x$. The endomorphism $F_1 : C_1 \to C_1$ is required by `hF₁c` to make $(F_1, c_1, c_1, \operatorname{Spec}(\mathrm{frobenius}\ k\ p))$ a pullback square, and by `hF₁X` to satisfy that $F_1$ followed by $i_1$ followed by the first projection of `baseChange A X k` equals $i_1$ followed by that projection. Finally $F_{1k}$ is an endomorphism of `pullback c₁ (𝟙 (Spec k))` with `hF₁k₁` and `hF₁k₂` asserting that it commutes with the first projection via $F_1$ and with the second projection via $\operatorname{Spec}(\mathrm{frobenius}\ k\ p)$.
--
--   Conclusion. For all $g, g' \in J_I$: if the pull-back of the Poincaré bundle of `hrep₁.some` along the point `ptsI g'` is isomorphic to the pull-back along $F_{1k}$ of the pull-back of that Poincaré bundle along `ptsI g`, then $\theta_1 g' =$ `frobIg` $\cdot\, \theta_1 g$, the action being that of semilinear automorphisms on $\operatorname{Pic}^0$ of the Igusa function field.
--
--   This is the index-$1$ half of the transport of the Frobenius twist through the Abel–Jacobi dictionary on the special fibre at $p$ of the Jacobian of $X_1(Mp)$: it identifies the operation induced on $\operatorname{Pic}^0$ of the cuspidal Igusa component by pulling rigidified line bundles back along the Frobenius square with the coefficientwise $p$-power map of the Igusa function field inside $k(\!(q)\!)$. It is used in the companion statement describing the first component of `G.proj` on points coming from a Frobenius composite, in the analysis of the Galois action on the component groups of the Néron model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_addEquiv_eq_frob_smul_of_nonempty_poincare_pullbackAlong_iso_pullback_frobeniusTwist_fst_twoChartModel_x1_mul.lean

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
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.addEquiv_eq_frob_smul_of_nonempty_poincare_pullbackAlong_iso_pullback_frobeniusTwist_fst_twoChartModel_x1_mul
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

    (G : ModularCurve.JOneP.NeronSpecialFibreGeom p)
    (pts : G.J0s ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase)
    (ptsI : G.JI ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₁.toBase)
    (ptsE : G.JE ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₂.toBase)
    (hadd : ∀ a b : G.J0s, Nonempty
      ((hreps.poincare.pullbackAlong (pts (a + b))).L ≅
        (hreps.poincare.pullbackAlong (pts a)).L ⊗ (hreps.poincare.pullbackAlong (pts b)).L))
    (haddI : ∀ a b : G.JI, Nonempty
      ((hrep₁.some.poincare.pullbackAlong (ptsI (a + b))).L ≅
        (hrep₁.some.poincare.pullbackAlong (ptsI a)).L ⊗ (hrep₁.some.poincare.pullbackAlong (ptsI b)).L))
    (haddE : ∀ a b : G.JE, Nonempty
      ((hrep₂.some.poincare.pullbackAlong (ptsE (a + b))).L ≅
        (hrep₂.some.poincare.pullbackAlong (ptsE a)).L ⊗ (hrep₂.some.poincare.pullbackAlong (ptsE b)).L))
    (hproj : ∀ x : G.J0s,
      ptsI (G.proj x).1 =
        postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) (pts x) ∧
      ptsE (G.proj x).2 = postComp ν₂ (pts x))

    (w : ModularCurve.IntegralWeightOneForm k M)
    (Mdl₁ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₁ : Mdl₁.C ≅ C₁)
    (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)

    [hne₁ : Nonempty (Scheme.Opens.toScheme ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hgauss₁ : ∀ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
      y.map (algebraMap A k) ≠ 0 →
      ((a : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      ((Mdl₁.ffEquiv.symm
          (Mdl₁.C.germToFunctionField ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) =
        HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) / HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k)))

    (θ₁ : G.JI ≃+ AlgebraicCurve.Pic0 k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hθpin₁ : ∀ (g : G.JI) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
      Nonempty ((hrep₁.some.poincare.pullbackAlong (ptsI g)).L ≅
        (RelEffCartierDiv.ofPoint c₁ x.1 x.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₁ ε₁.1 ε₁.2).idealModule) →
      ∃ Dv : Divisor.degZero (K := k) (F := ↥(ModularCurve.igusaFunctionFieldX1C k M w)),
        (Dv : Divisor k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) =
          Finsupp.single (Mdl₁.pointEquivPlace ⟨x.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact x.2⟩) 1 -
            Finsupp.single (Mdl₁.pointEquivPlace ⟨ε₁.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact ε₁.2⟩) 1 ∧
        θ₁ g = Pic0.mk Dv)

    (frobIg : SemilinearAut k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hfrobIg : ∀ (x : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (n : ℤ),
      ((frobIg • x : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k).coeff n = ((x : LaurentSeries k).coeff n) ^ p)

    (F₁ : C₁ ⟶ C₁) (hF₁c : IsPullback F₁ c₁ c₁ (Spec.map (CommRingCat.ofHom (frobenius k p))))
    (hF₁X : F₁ ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))

    (F₁k : pullback c₁ (𝟙 (Spec (CommRingCat.of k))) ⟶ pullback c₁ (𝟙 (Spec (CommRingCat.of k))))
    (hF₁k₁ : F₁k ≫ pullback.fst c₁ (𝟙 (Spec (CommRingCat.of k))) = pullback.fst c₁ (𝟙 (Spec (CommRingCat.of k))) ≫ F₁)
    (hF₁k₂ : F₁k ≫ pullback.snd c₁ (𝟙 (Spec (CommRingCat.of k))) =
      pullback.snd c₁ (𝟙 (Spec (CommRingCat.of k))) ≫ Spec.map (CommRingCat.ofHom (frobenius k p))) :

    ∀ (g g' : G.JI),
      Nonempty ((hrep₁.some.poincare.pullbackAlong (ptsI g')).L ≅
        (Scheme.Modules.pullback F₁k).obj (hrep₁.some.poincare.pullbackAlong (ptsI g)).L) →
      θ₁ g' = frobIg • θ₁ g := by sorry
