-- Prove2me | Theorems.Thm_ModularCurve_XOneP_pointEquivPlace_eq_frob_smul_pointEquivPlace_of_comp_eq_frobenius_comp_of_gaussReading_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.pointEquivPlace_eq_frob_smul_pointEquivPlace_of_comp_eq_frobenius_comp_of_gaussReading_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/757596ee-73c6-540e-878a-92993b7ce08c
-- title:
--   Frobenius twist of a point twists its Igusa place by `frobIg`
-- statement:
--   **Arithmetic data.** Fix a prime $p$ and a natural number $M$ with $5 \le M$ and $p \nmid M$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ for the set $\{p\}$, and let $\zeta \in L$ be a primitive $p$-th root of unity. Let $K$ be an intermediate field of $L \subseteq L((q))$ (`LaurentSeries L`), subject to `hK`: $K$ equals [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), the subfield of $L((q))$ generated over $L$ by the image of the function field of $X_1(Mp)$ over $\mathbb{Q}$ under the coefficientwise embedding [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81). Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ (`hAp`) and $\zeta$ lies in the image of $A \to L$ (`hζA`), with $K$ an $A$-algebra compatibly with $A \to L \to K$. Let $j \in K$ be an element whose Laurent expansion is the image under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular invariant (`hj`), with $j \neq 0$. Let $k$ be an algebraically closed field of characteristic $p$ which is an $A$-algebra.
--
--   **The two components of the special fibre.** Write [`ModularCurve.TwoChart.modelTo A ↥K j`](def/ModularCurve_TwoChartModel.html#L252) for the structure morphism of the two-chart model of $K$ with respect to $j$ over $\operatorname{Spec} A$, and `baseChange A (ModularCurve.TwoChart.modelTo A ↥K j) k` for its base change along $\operatorname{Spec} k \to \operatorname{Spec} A$, i.e. the second projection of $\operatorname{pullback}$ of the model along `specMap A k`. Let $C_1, C_2$ be schemes with morphisms $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$, each proper, smooth of relative dimension $1$ and geometrically integral, and let $i_1, i_2$ be morphisms over $\operatorname{Spec} k$ from $c_1$, $c_2$ to the base-changed model, each a closed immersion. Three hypotheses constrain this configuration: `hcover`, that every point of the base-changed model lies in the range of the underlying map of $i_1$ or in that of $i_2$; `hred`, that the fibre product of $i_1$ and $i_2$ is reduced; and, for a natural number $n$, `hn` and `hn0`, that this fibre product has exactly $n$ points and $0 < n$.
--
--   **Sections.** Let $\varepsilon$ be a section of the two-chart model over $\operatorname{Spec} A$, and $\varepsilon_1$, $\varepsilon_2$ sections of $c_1$, $c_2$ over $\operatorname{Spec} k$; the hypothesis `hε₁` requires that $\varepsilon_1$ followed by $i_1$ be the base-changed section `sectionBaseChange k ε`.
--
--   **Relative Picard data.** Let $D$ be a `RelativePic0Designation` for the two-chart model over $A$ (a scheme with a structure morphism `D.toBase` to $\operatorname{Spec} A$ and a zero section), with `hrep` asserting that the type of data `RepresentsRelSubPic` for the model, $\varepsilon$, the condition `algEquivZeroCut` (rigidified line bundles whose fibres over algebraically closed points are algebraically equivalent to zero) and $D$ is nonempty: such data consist of a Poincaré rigidified bundle on `D.toBase` satisfying the condition, universal for it, and trivialised along the zero section. The hypotheses `hsm` and `hsep` require `D.toBase` to be smooth and separated. The hypothesis `hreps` provides the corresponding representability datum over $k$, for the base-changed model, the section `sectionBaseChange k ε` and the designation `D.baseChange k`, and `hPk` requires its Poincaré bundle to be isomorphic to the one obtained from the Poincaré bundle of `hrep.some` by pulling back along the first projection of `pullback D.toBase (specMap A k)` and applying `BaseChange.ofR`. Further, $D_1$ and $D_2$ are relative $\mathrm{Pic}^0$ designations over $k$ for $c_1$ and $c_2$, with `hrep₁`, `hrep₂` asserting representability for $(c_1,\varepsilon_1)$ and $(c_2,\varepsilon_2)$ with respect to the same condition.
--
--   **The map to the second component.** Let $\nu_2$ be a morphism over $\operatorname{Spec} k$ from `(D.baseChange k).toBase` to `D₂.toBase`, characterised by `hν₂`: for every scheme $T$ over $k$ and every $T$-point $a$ of `(D.baseChange k).toBase` over $k$, the Poincaré bundle of `hrep₂.some` pulled back along $a$ followed by $\nu_2$ is isomorphic to the rigidification, along `rigSection c₂ t ε₂` and the projection `pullback.snd c₂ t`, of the pullback along `curveChange i₂.1` of the Poincaré bundle of `hreps` pulled back along $a$.
--
--   **Group-theoretic frame of the special fibre.** Let $G$ be a [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9): abelian groups `G.J0s`, `G.JI`, `G.JE`, a subgroup `G.torus` of `G.J0s`, and a surjective homomorphism `G.proj : G.J0s →+ G.JI × G.JE` with kernel `G.torus`. Bijections `pts`, `ptsI`, `ptsE` identify `G.J0s`, `G.JI`, `G.JE` with the sets of sections over $\operatorname{Spec} k$ of `(D.baseChange k).toBase`, `D₁.toBase`, `D₂.toBase` respectively. The hypotheses `hadd`, `haddI`, `haddE` require each of these bijections to be additive in the sense that the Poincaré pullback at $a+b$ is isomorphic to the tensor product of the Poincaré pullbacks at $a$ and at $b$ (for `hreps`, `hrep₁.some`, `hrep₂.some` respectively). The hypothesis `hproj` requires, for every $x \in$ `G.J0s`, that `ptsI (G.proj x).1` be `pts x` followed by the morphism `RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some` and that `ptsE (G.proj x).2` be `pts x` followed by $\nu_2$.
--
--   **The Igusa model of the first component.** Let $w$ be a [`ModularCurve.IntegralWeightOneForm k M`](def/ModularCurve_IgusaFunctionFieldX1.html#L16) (a weight one modular form for $\Gamma_1(M)$ together with an integral $q$-expansion whose reduction over $k$ is nonzero), and let `Mdl₁` be a `CurveModel` over $k$ for the Igusa function field [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35), an intermediate field of $k((q))$: thus an integral proper smooth curve `Mdl₁.C` over $k$, a ring isomorphism `Mdl₁.ffEquiv` of that field with the function field of `Mdl₁.C` compatible with $k$, and a bijection between closed points of `Mdl₁.C` and places of the Igusa field over $k$ matching stalks with valuation subrings. An isomorphism $e_1 :$ `Mdl₁.C` $\cong C_1$ is given with `he₁`: $e_1$ followed by $c_1$ is `Mdl₁.toBase`. The hypothesis `hne₁` asserts that the open subscheme of `Mdl₁.C` obtained as the preimage, under $e_1$ followed by $i_1$ followed by the projection of the base change to the two-chart model, of the image of the finite chart [`ModularCurve.TwoChart.ιFin A ↥K j`](def/ModularCurve_TwoChartModel.html#L231) is nonempty. The Gauss-reading hypothesis `hgauss₁` states: for every element $a$ of the finite chart algebra [`ModularCurve.TwoChart.chartAlgFin A ↥K j`](def/ModularCurve_TwoChartModel.html#L135) and all power series $x, y$ over $A$ such that the reduction of $y$ to $k$ is nonzero and $a \cdot y = x$ holds in $L((q))$ after mapping $x, y$ to $L$, the Laurent expansion of the element of the Igusa field obtained by transporting $a$ — via the global sections of the finite chart, the pullback along $e_1$ followed by $i_1$ followed by the projection, the germ at the generic point, and `Mdl₁.ffEquiv.symm` — equals the quotient of the reduction of $x$ by the reduction of $y$ in $k((q))$.
--
--   **Abel–Jacobi normalisation and Frobenius.** Let $\theta_1$ be an additive equivalence of `G.JI` with $\mathrm{Pic}^0$ of the Igusa function field over $k$, subject to `hθpin₁`: for every $g \in$ `G.JI` and every section $x$ of $c_1$ over $\operatorname{Spec} k$, if the Poincaré bundle of `hrep₁.some` pulled back along `ptsI g` is isomorphic to the tensor product of the line bundle of the relative effective Cartier divisor of the point $x$ with the ideal module of the relative effective Cartier divisor of the point $\varepsilon_1$, then there exists a degree-zero divisor $Dv$ of the Igusa field over $k$ equal to $\delta_{v(x)} - \delta_{v(\varepsilon_1)}$, where $v(\cdot)$ denotes the place `Mdl₁.pointEquivPlace` of the corresponding section of `Mdl₁.toBase` obtained by composing with $e_1^{-1}$, and such that $\theta_1 g$ is the class of $Dv$. Finally, let `frobIg` be a `SemilinearAut` of the Igusa function field over $k$, that is a pair consisting of a ring automorphism of the field and one of $k$ which are compatible with the structure map, subject to `hfrobIg`: for every element $x$ of the Igusa field and every $n \in \mathbb{Z}$, the $n$-th Laurent coefficient of `frobIg • x` is the $p$-th power of the $n$-th Laurent coefficient of $x$.
--
--   **Conclusion.** For all sections $c, c'$ of $c_1$ over $\operatorname{Spec} k$: if $c'$ followed by $i_1$ followed by the projection from the base-changed model to the two-chart model equals $\operatorname{Spec}$ of the $p$-power endomorphism `frobenius k p` of $k$ followed by $c$ followed by $i_1$ followed by that same projection, then
--   $$\mathtt{Mdl₁.pointEquivPlace}\,(c' \text{ followed by } e_1^{-1}) \;=\; \mathtt{frobIg} \cdot \mathtt{Mdl₁.pointEquivPlace}\,(c \text{ followed by } e_1^{-1}),$$
--   an equality of places of the Igusa function field [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35) over $k$, where $\cdot$ is the action of semilinear automorphisms on places and the two sections of `Mdl₁.toBase` are obtained from $c'$, $c$ by composing with $e_1^{-1}$, using `he₁` to verify the section condition.
--
--   This is the point-level form of the Frobenius compatibility on the Igusa component of the special fibre at $p$ of $X_1(Mp)$: an arithmetic Frobenius twist of a $k$-point of that component translates, under the identification of closed points with places of the Igusa function field, into the coefficientwise $p$-power automorphism of the Igusa field. It feeds the Frobenius reading of the special fibre of $J_1(Mp)$ through the Abel–Jacobi dictionary, and is cited by the statements identifying the action of `frobIg` on $\mathrm{Pic}^0$ classes, on the first projection of the special-fibre group, and in the Hecke divisor computation over the reduced model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_pointEquivPlace_eq_frob_smul_pointEquivPlace_of_comp_eq_frobenius_comp_of_gaussReading_twoChartModel_x1_mul.lean

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

theorem ModularCurve.XOneP.pointEquivPlace_eq_frob_smul_pointEquivPlace_of_comp_eq_frobenius_comp_of_gaussReading_twoChartModel_x1_mul
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
      ((frobIg • x : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k).coeff n = ((x : LaurentSeries k).coeff n) ^ p) :
    ∀ (c c' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
      c'.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
        Spec.map (CommRingCat.ofHom (frobenius k p)) ≫ c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) →
      Mdl₁.pointEquivPlace ⟨c'.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact c'.2⟩ =
        frobIg • Mdl₁.pointEquivPlace ⟨c.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact c.2⟩ := by sorry
