-- Prove2me | Theorems.Thm_ModularCurve_XOneP_addEquiv_proj_fst_eq_pic0Mk_single_sub_single_of_points_eq_reduction_of_poincare_iso_ofPoint_valuationSubring_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.addEquiv_proj_fst_eq_pic0Mk_single_sub_single_of_points_eq_reduction_of_poincare_iso_ofPoint_valuationSubring_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/00e1fb1a-0673-5e7a-ac90-08fb3ac5b5d3
-- title:
--   Igusa-component class of the reduction of 𝒪(ξ₁)⊗𝒪(ξ₂)⁻¹
-- statement:
--   The data of the statement fall into eight groups.
--
--   **Arithmetic base.** A prime $p$, a nonzero natural number $M$ with $5 \le M$ (`hM`) and $p \nmid M$ (`hpM`); a field $L$ of characteristic zero that is a cyclotomic extension of $\mathbb Q$ of type $\{p\}$, and $\zeta \in L$ a primitive $p$-th root of unity (`hζ`); an intermediate field $K$ of $L \subseteq L((t))$ with `hK` requiring $K$ to be [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), the subfield of $L((t))$ generated over $L$ by the coefficientwise image of the function field of $X_1(Mp)$ over $\mathbb Q$; a discrete valuation domain $A$ with $L$ as its fraction field, such that $p$ lies in the maximal ideal of $A$ (`hAp`) and $\zeta$ lies in the image of $A$ in $L$ (`hζA`), together with an $A$-algebra structure on $K$ compatible with the tower $A \to L \to K$; and an element $j \in K$ whose image in $L((t))$ is the coefficientwise image [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81) of the $q$-expansion of the $j$-function (`hj`), with $j \ne 0$. All of what follows concerns the two-chart model $\pi =$ [`ModularCurve.TwoChart.modelTo A (↥K) j`](def/ModularCurve_TwoChartModel.html#L252), the morphism from the pushout of the two affine charts [`ModularCurve.TwoChartModel A (↥K) j`](def/ModularCurve_TwoChartModel.html#L229) to $\operatorname{Spec} A$, which is assumed proper; also fixed are algebra structures on $\overline{\mathbb Q}$ over $A$ and over $L$, compatibly.
--
--   **Special fibre and its two components.** An algebraically closed field $k$ of characteristic $p$, an $A$-algebra, so that the special fibre is the pullback of $\pi$ along `specMap A k` with structure morphism `baseChange A π k = pullback.snd`. Two schemes $C_1, C_2$ with morphisms $c_1, c_2$ to $\operatorname{Spec} k$ that are proper, smooth of relative dimension $1$ and geometrically integral, and morphisms $i_1 : C_1 \to$ special fibre, $i_2 : C_2 \to$ special fibre over $c_1$, $c_2$ respectively (elements of `SchemeHomOver`, i.e. $i_1.1$ composed with `baseChange A π k` is $c_1$, and likewise for $i_2$), both closed immersions. The hypothesis `hcover` requires every point of the special fibre to lie in the range of the underlying map of $i_1$ or of $i_2$; `hred` requires the scheme-theoretic intersection `pullback i₁.1 i₂.1` to be reduced, and $n$ is a natural number with `Nat.card` of the underlying type of that intersection equal to $n$ (`hn`) and $0 < n$ (`hn0`).
--
--   **Sections.** A section $\varepsilon$ of $\pi$ over $\operatorname{Spec} A$, sections $\varepsilon_1$ of $c_1$ and $\varepsilon_2$ of $c_2$ over $\operatorname{Spec} k$, and `hε₁` requiring $\varepsilon_1$ followed by $i_1$ to equal `sectionBaseChange k ε`, the base change of $\varepsilon$ to the special fibre.
--
--   **Relative $\mathrm{Pic}^0$ data.** A designation $D$ for $\pi$ (a scheme with a structure morphism `D.toBase` to $\operatorname{Spec} A$ and a zero section), with `hrep` asserting that $D$ represents, with Poincaré bundle `hrep.some.poincare`, the subfunctor `algEquivZeroCut π ε` of $\varepsilon$-rigidified line bundles on $\pi$ whose restriction to every geometric fibre is algebraically equivalent to zero; `hsm` and `hsep` require `D.toBase` to be smooth and separated. The hypothesis `hreps` is the corresponding representability statement over $k$: the designation `D.baseChange k` represents `algEquivZeroCut` for the base-changed curve and the section `sectionBaseChange k ε`. The hypothesis `hPk` requires the Poincaré bundle `hreps.poincare.L` to be isomorphic to `BaseChange.ofR` applied to the pullback of `hrep.some.poincare` along the first projection of `pullback D.toBase (specMap A k)`. Further, designations $D_1$ for $(c_1,\varepsilon_1)$ and $D_2$ for $(c_2,\varepsilon_2)$ over $k$, with representability hypotheses `hrep₁`, `hrep₂`. Finally a morphism $\nu_2$ from `(D.baseChange k).toBase` to `D₂.toBase` over $\operatorname{Spec} k$ together with `hν₂`: for every scheme $T$ with a morphism $t$ to $\operatorname{Spec} k$ and every $T$-point $a$ of `(D.baseChange k).toBase`, the bundle of `hrep₂.some.poincare.pullbackAlong (schemeHomOverComp a ν₂)` is isomorphic to `Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)` applied to the pullback along `curveChange i₂.1 i₂.2 t` of the bundle of `hreps.poincare.pullbackAlong a`; thus $\nu_2$ implements restriction of line bundles from the special fibre to $C_2$, rigidified along $\varepsilon_2$.
--
--   **The special-fibre group dictionary.** An object $G$ of [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9), consisting of abelian groups `G.J0s`, `G.JI`, `G.JE`, a subgroup `G.torus` of `G.J0s` and a surjective homomorphism `G.proj : G.J0s →+ G.JI × G.JE` with kernel `G.torus`. Bijections `pts`, `ptsI`, `ptsE` identify `G.J0s`, `G.JI`, `G.JE` with the $k$-points of `(D.baseChange k).toBase`, `D₁.toBase`, `D₂.toBase` respectively. The hypotheses `hadd`, `haddI`, `haddE` require each bijection to be compatible with addition in the Picard sense: for all $a, b$, the Poincaré pullback at the image of $a+b$ is isomorphic to the tensor product of the Poincaré pullbacks at the images of $a$ and of $b$ (for `hreps`, `hrep₁.some`, `hrep₂.some` respectively). The hypothesis `hproj` requires, for every $x$ in `G.J0s`, that `ptsI (G.proj x).1` be the point obtained from `pts x` by postcomposition with `RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some`, and that `ptsE (G.proj x).2` be the point obtained from `pts x` by postcomposition with $\nu_2$.
--
--   **Igusa model of $C_1$ and the Abel–Jacobi pinning.** An integral weight one form $w$ of level $M$ over $k$ (a weight one modular form on $\Gamma_1(M)$ with an integral $q$-expansion whose reduction is nonzero), a curve model `Mdl₁` over $k$ of the Igusa function field [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35), an isomorphism $e_1 :$ `Mdl₁.C` $\cong C_1$ with `he₁` requiring $e_1$ followed by $c_1$ to equal `Mdl₁.toBase`, and an additive equivalence $\theta_1$ from `G.JI` to $\mathrm{Pic}^0$ of the Igusa function field over $k$. The hypothesis `hθpin₁` requires: for every $g$ in `G.JI` and every $k$-point $x$ of $c_1$, if the bundle of `hrep₁.some.poincare.pullbackAlong (ptsI g)` is isomorphic to the tensor product of the line bundle of `RelEffCartierDiv.ofPoint c₁ x` with the ideal module of `RelEffCartierDiv.ofPoint c₁ ε₁` (that is, to $\mathcal O(x) \otimes \mathcal O(\varepsilon_1)^{-1}$), then there is a degree-zero divisor $Dv$ on the Igusa function field whose underlying finitely supported function equals `Finsupp.single` at the place attached by `Mdl₁.pointEquivPlace` to $x$ transported along $e_1^{-1}$ with value $1$, minus `Finsupp.single` at the place attached to $\varepsilon_1$ transported along $e_1^{-1}$ with value $1$, and such that $\theta_1 g$ is the class `Pic0.mk Dv`.
--
--   **Smooth locus.** An open subscheme $U$ of the two-chart model such that the restriction of $\pi$ to $U$ is smooth of relative dimension $1$, and `hUmax` requiring every open $W$ with that property to satisfy $W \le U$.
--
--   **The place.** A valuation subring $\mathrm{Pl}$ of $\overline{\mathbb Q}$ with $p$ a non-unit of $\mathrm{Pl}$ (`hPl`), a ring homomorphism $\rho : A \to \mathrm{Pl}$ whose composite with the inclusion of $\mathrm{Pl}$ in $\overline{\mathbb Q}$ is the structure map $A \to \overline{\mathbb Q}$ (`hρ`), and a ring homomorphism $\pi_k : \mathrm{Pl} \to k$ with $A \to k$ equal to $\pi_k \circ \rho$ (`hAlgk`) and $\pi_k$ surjective (`hπk`).
--
--   **Conclusion.** For all $\xi_1, \xi_2$ in `SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) π`, that is, morphisms from $\operatorname{Spec} \mathrm{Pl}$ to the two-chart model whose composite with $\pi$ is $\operatorname{Spec}$ of $\rho$, and for all $k$-points $d_1, d_2$ of $c_1$ (both are sections of $c_1$, on $C_1$), subject to: the ranges of the underlying maps of $\xi_1$ and of $\xi_2$ are contained in $U$; $d_1$ followed by $i_1$ and then by the first projection of the special fibre equals $\operatorname{Spec}$ of $\pi_k$ followed by $\xi_1$, and the image of the closed point of $\operatorname{Spec} k$ under $d_1$ followed by $i_1$ does not lie in the range of the underlying map of $i_2$; and the same two conditions for $d_2$ and $\xi_2$ — the following holds. For every $s$ in `SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase` such that the bundle of `hrep.some.poincare.pullbackAlong s` is isomorphic to the tensor product of the line bundle of `RelEffCartierDiv.ofPoint π ξ₁` with the ideal module of `RelEffCartierDiv.ofPoint π ξ₂` (that is, to $\mathcal O(\xi_1) \otimes \mathcal O(\xi_2)^{-1}$), for every $y$ in `G.J0s` whose point `pts y` followed by the first projection of `pullback D.toBase (specMap A k)` equals $\operatorname{Spec}$ of $\pi_k$ followed by $s$, and for every degree-zero divisor $\bar D$ on the Igusa function field whose underlying finitely supported function equals `Finsupp.single` at the place attached by `Mdl₁.pointEquivPlace` to $d_1$ transported along $e_1^{-1}$ with value $1$ minus `Finsupp.single` at the place attached to $d_2$ transported along $e_1^{-1}$ with value $1$, one has
--   $$\theta_1\bigl((G.\mathrm{proj}\, y)_1\bigr) = \mathrm{Pic}^0\text{-class of } \bar D .$$
--
--   This is the computational heart of the Raynaud-style dictionary for the special fibre at $p$ of the relative $\mathrm{Pic}^0$ of the two-chart model of $X_1(Mp)$: the class in $\mathrm{Pic}^0$ of the Igusa curve of the reduction of a point classifying $\mathcal O(\xi_1) \otimes \mathcal O(\xi_2)^{-1}$ is read off as the difference of the two reduced points, provided both reductions avoid the second component. It is used in the passage from single differences of points to arbitrary degree-zero divisors, and in the construction of points of $\mathrm{Pic}^0$ whose Igusa component is prescribed and whose Eisenstein-component part vanishes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_addEquiv_proj_fst_eq_pic0Mk_single_sub_single_of_points_eq_reduction_of_poincare_iso_ofPoint_valuationSubring_twoChartModel_x1_mul.lean

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
import Definitions.Def_ModularCurve_X1HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.addEquiv_proj_fst_eq_pic0Mk_single_sub_single_of_points_eq_reduction_of_poincare_iso_ofPoint_valuationSubring_twoChartModel_x1_mul
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

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

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

    (θ₁ : G.JI ≃+ AlgebraicCurve.Pic0 k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hθpin₁ : ∀ (g : G.JI) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
      Nonempty ((hrep₁.some.poincare.pullbackAlong (ptsI g)).L ≅
        (RelEffCartierDiv.ofPoint c₁ x.1 x.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₁ ε₁.1 ε₁.2).idealModule) →
      ∃ Dv : Divisor.degZero (K := k) (F := ↥(ModularCurve.igusaFunctionFieldX1C k M w)),
        (Dv : Divisor k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) =
          Finsupp.single (Mdl₁.pointEquivPlace ⟨x.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact x.2⟩) 1 -
            Finsupp.single (Mdl₁.pointEquivPlace ⟨ε₁.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact ε₁.2⟩) 1 ∧
        θ₁ g = Pic0.mk Dv)

    (U : (ModularCurve.TwoChartModel A (↥K) j).Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j))]
    (hUmax : ∀ W : (ModularCurve.TwoChartModel A (↥K) j).Opens, SmoothOfRelativeDimension 1 (W.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j)) → W ≤ U)

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ)

    (hπk : Function.Surjective πk) :
    ∀ (ξ₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j)) (ξ₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j))
      (d₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (d₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
      Set.range ξ₁.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j)) → Set.range ξ₂.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j)) →
      d₁.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ ξ₁.1 →
      (d₁.1 ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base →
      d₂.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ ξ₂.1 →
      (d₂.1 ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base →
      ∀ (s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase),
        Nonempty ((hrep.some.poincare.pullbackAlong s).L ≅
          (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) ξ₁.1 ξ₁.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) ξ₂.1 ξ₂.2).idealModule) →
        ∀ (y : G.J0s),
          (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ s.1 →
          ∀ (Dbar : Divisor.degZero (K := k) (F := ↥(ModularCurve.igusaFunctionFieldX1C k M w))),
            (Dbar : Divisor k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) =
              Finsupp.single (Mdl₁.pointEquivPlace ⟨d₁.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact d₁.2⟩) 1 -
                Finsupp.single (Mdl₁.pointEquivPlace ⟨d₂.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact d₂.2⟩) 1 →
            θ₁ (G.proj y).1 = Pic0.mk Dbar := by sorry
