-- Prove2me | Theorems.Thm_ModularCurve_XOneP_addEquiv_proj_snd_eq_pic0Mk_single_sub_single_of_points_eq_reduction_of_poincare_iso_ofPoint_valuationSubring_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.addEquiv_proj_snd_eq_pic0Mk_single_sub_single_of_points_eq_reduction_of_poincare_iso_ofPoint_valuationSubring_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/dbdf4c93-03fa-53bc-ba98-f815dd4529dc
-- title:
--   Reduction of 𝒪(ξ₁)⊗𝒪(ξ₂)⁻¹ read on the Igusa component
-- statement:
--   Throughout, $p$ is a prime and $M$ a non-zero natural number with $5\le M$ and $p\nmid M$. The field $L$ has characteristic zero and is a cyclotomic extension of $\mathbb Q$ of type $\{p\}$, with $\zeta\in L$ a primitive $p$-th root of unity; $K$ is an intermediate field of $L\subseteq$ `LaurentSeries L` and the hypothesis `hK` identifies it with [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. with the subfield of `LaurentSeries L` generated over $L$ by the image, under coefficientwise extension of scalars, of the rational function field of $X_1(Mp)$ over $\mathbb Q$. The ring $A$ is a discrete valuation domain with fraction field $L$, subject to `hAp` ($p$ lies in the maximal ideal of $A$) and `hζA` ($\zeta$ lies in the image of $A\to L$), and $K$ is an $A$-algebra compatibly with $A\to L\to K$. The element $j\in K$ is non-zero and, by `hj`, has image in `LaurentSeries L` the coefficientwise image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157). Finally $k$ is an algebraically closed field of characteristic $p$ and an $A$-algebra.
--
--   Write $X:=$ [`ModularCurve.TwoChartModel A K j`](def/ModularCurve_TwoChartModel.html#L229) with structure morphism $f:=$ [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) to $\operatorname{Spec}A$, assumed proper, and write $X_k$ for the fibre product of $f$ with $\operatorname{Spec}k\to\operatorname{Spec}A$, with structure morphism `baseChange A f k` (the second projection). Recall that for morphisms $g,h$ over a common base, `SchemeHomOver g h` denotes the pairs consisting of a morphism $\varphi$ together with the identity $\varphi$ followed by $h$ equals $g$.
--
--   Components of the special fibre: $C_1,C_2$ are schemes with morphisms $c_1,c_2$ to $\operatorname{Spec}k$, each proper, smooth of relative dimension $1$ and geometrically integral, and $i_1,i_2$ are closed immersions of $C_1,C_2$ into $X_k$ over $\operatorname{Spec}k$. The hypothesis `hcover` says that every point of $X_k$ lies in the image of $i_1$ or of $i_2$; `hred` says the fibre product of $i_1$ and $i_2$ is reduced; $n$ is a natural number with `hn` asserting that the number of points of that fibre product is $n$, and `hn0` that $n>0$.
--
--   Sections: $\varepsilon$ is a section of $f$ over $\operatorname{Spec}A$, and $\varepsilon_1,\varepsilon_2$ are sections of $c_1,c_2$ over $\operatorname{Spec}k$, with `hε₁` asserting that $\varepsilon_1$ followed by $i_1$ is the base-changed section `sectionBaseChange k ε`.
--
--   Relative Picard data: $D$ is a `RelativePic0Designation` for $f$ (a scheme with a structure morphism to $\operatorname{Spec}A$ and a zero section), `hrep` asserts that $D$ represents, with rigidification along $\varepsilon$, the subfunctor of rigidified line bundles cut out by the fibrewise algebraic-equivalence-to-zero condition `algEquivZeroCut`; `hsm` and `hsep` say that $D$'s structure morphism is smooth and separated. Likewise `hreps` is a representability datum for the base change of $f$ to $k$, rigidified along `sectionBaseChange k ε`, represented by `D.baseChange k`, and `hPk` asserts that its Poincaré bundle is isomorphic to the bundle obtained from the Poincaré bundle of `hrep.some`, pulled back along the first projection $D\times_{\operatorname{Spec}A}\operatorname{Spec}k\to D$ and transported by `BaseChange.ofR`. Similarly $D_1$ and $D_2$ are designations for $c_1$ and $c_2$, with representability data `hrep₁`, `hrep₂` relative to $\varepsilon_1$, $\varepsilon_2$.
--
--   The morphism $\nu_2$ goes from `(D.baseChange k).toBase` to `D₂.toBase` over $\operatorname{Spec}k$, and `hν₂` characterises it: for every scheme $T$ over $\operatorname{Spec}k$ with structure morphism $t$ and every $T$-point $a$ of `(D.baseChange k).toBase`, the pullback along $a$ followed by $\nu_2$ of the Poincaré bundle of `hrep₂.some` is isomorphic to the rigidification, along the section `rigSection c₂ t ε₂` and the projection `pullback.snd c₂ t`, of the restriction along `curveChange i₂` of the pullback along $a$ of the Poincaré bundle of `hreps` (here `rigidify σ q L` is $L\otimes q^*(({\sigma}^*L)^\vee)$).
--
--   Global embeddings: $A$ and $L$ are algebras over $\overline{\mathbb Q}:=$ `AlgebraicClosure ℚ` in a compatible tower.
--
--   Special-fibre group data: $G$ is a [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9), that is, abelian groups `G.J0s`, `G.JI`, `G.JE`, a subgroup `G.torus` of `G.J0s` and a surjective homomorphism `G.proj : G.J0s →+ G.JI × G.JE` with kernel `G.torus`. The bijections `pts`, `ptsI`, `ptsE` identify `G.J0s`, `G.JI`, `G.JE` with the $k$-points of `(D.baseChange k).toBase`, `D₁.toBase`, `D₂.toBase` respectively. The hypotheses `hadd`, `haddI`, `haddE` express additivity of these three bijections: the Poincaré pullback at a sum of two elements is isomorphic to the tensor product of the two Poincaré pullbacks. The hypothesis `hproj` says that for every $x\in$ `G.J0s`, the point `ptsI ((G.proj x).1)` is $x$'s point composed with the morphism `RepresentsRelSubPic.pullbackHom` attached to $i_1$ and `hε₁`, and `ptsE ((G.proj x).2)` is $x$'s point composed with $\nu_2$.
--
--   Identification of $C_2$ with an Igusa curve: $w$ is an [`ModularCurve.IntegralWeightOneForm k M`](def/ModularCurve_IgusaFunctionFieldX1.html#L16), i.e. a weight-one modular form on $\Gamma_1(M)$ together with an integral power series realising its $q$-expansion and with non-vanishing reduction constant over $k$; `Mdl₂` is a `CurveModel` over $k$ for the field [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35), $e_2$ is an isomorphism of `Mdl₂.C` with $C_2$ and `he₂` says that $e_2$ followed by $c_2$ is `Mdl₂.toBase`. The isomorphism $\theta_2$ identifies `G.JE` with [`AlgebraicCurve.Pic0 k (igusaFunctionFieldX1C k M w)`](def/AlgebraicCurve_DivisorClassGroup.html#L223), the group of degree-zero divisors (finitely supported $\mathbb Z$-valued functions on places) modulo principal ones. The Abel–Jacobi normalisation `hθpin₂` requires: for every $g\in$ `G.JE` and every $k$-point $x$ of $C_2$, if the Poincaré pullback of `hrep₂.some` at `ptsE g` is isomorphic to the line bundle of the relative effective Cartier divisor `ofPoint c₂ x` tensored with the ideal module of `ofPoint c₂ ε₂` (the graph ideal sheaf of $x$, dualised, tensored with the graph ideal sheaf of $\varepsilon_2$), then there is a degree-zero divisor $D_v$ whose underlying divisor is the difference of the indicator divisors at the places attached by `Mdl₂.pointEquivPlace` to $x$ followed by $e_2^{-1}$ and to $\varepsilon_2$ followed by $e_2^{-1}$, with $\theta_2 g=$ `Pic0.mk` $D_v$.
--
--   Smooth locus: $U$ is an open subscheme of $X$ whose structure morphism to $\operatorname{Spec}A$ is smooth of relative dimension $1$, and `hUmax` says that every open with that property is contained in $U$.
--
--   The place: $Pl$ is a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit in it, $\rho:A\to Pl$ satisfies that $\rho$ followed by the inclusion $Pl\subseteq\overline{\mathbb Q}$ is the structure map of $A$, $\pi_k:Pl\to k$ satisfies that $\rho$ followed by $\pi_k$ is the structure map $A\to k$, and `hπk` says $\pi_k$ is surjective.
--
--   Under these hypotheses the conclusion is the following. Let $\xi_1,\xi_2$ be $Pl$-points of $X$ over $\operatorname{Spec}A$ via $\rho$ (morphisms $\operatorname{Spec}Pl\to X$ whose composite with $f$ is $\operatorname{Spec}(\rho)$), and let $d_1,d_2$ be $k$-points of $C_2$. Assume: the image of the underlying map of $\xi_1$ is contained in $U$, and likewise for $\xi_2$; $d_1$ followed by $i_2$ followed by the first projection $X_k\to X$ equals $\operatorname{Spec}(\pi_k)$ followed by $\xi_1$, and the image of the closed point of $\operatorname{Spec}k$ under $d_1$ followed by $i_2$ does not lie in the image of $i_1$; $d_2$ followed by $i_2$ followed by the first projection equals $\operatorname{Spec}(\pi_k)$ followed by $\xi_2$, and the image of the closed point under $d_2$ followed by $i_2$ does not lie in the image of $i_1$. Assume further that $s$ is a $Pl$-point of `D.toBase` via $\operatorname{Spec}(\rho)$ such that the pullback along $s$ of the Poincaré bundle of `hrep.some` is isomorphic to the line bundle of `ofPoint f ξ₁` tensored with the ideal module of `ofPoint f ξ₂`; that $y\in$ `G.J0s` satisfies that the point `pts y` followed by the first projection $D\times_{\operatorname{Spec}A}\operatorname{Spec}k\to D$ equals $\operatorname{Spec}(\pi_k)$ followed by $s$; and that $\bar D$ is a degree-zero divisor of `igusaFunctionFieldX1C k M w` whose underlying divisor equals the indicator divisor at the place attached by `Mdl₂.pointEquivPlace` to $d_1$ followed by $e_2^{-1}$ minus the indicator divisor at the place attached to $d_2$ followed by $e_2^{-1}$. Then
--   $$\theta_2\bigl((G.\mathrm{proj}\,y).2\bigr)=\mathtt{Pic0.mk}\,\bar D .$$
--
--   This is the Abel–Jacobi reading, on the second (Igusa) component of the special fibre, of the class of $\mathcal O(\xi_1)\otimes\mathcal O(\xi_2)^{-1}$: the $\mathrm{Pic}^0$-point classifying that bundle reduces to an element of `G.J0s` whose $J_E$-projection is carried by $\theta_2$ to the divisor class $[d_1]-[d_2]$ of the Igusa function field. It is used by the statements that assemble such per-pair readings into divisors with arbitrary support and into the production of places and sections with prescribed reductions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_addEquiv_proj_snd_eq_pic0Mk_single_sub_single_of_points_eq_reduction_of_poincare_iso_ofPoint_valuationSubring_twoChartModel_x1_mul.lean

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

theorem ModularCurve.XOneP.addEquiv_proj_snd_eq_pic0Mk_single_sub_single_of_points_eq_reduction_of_poincare_iso_ofPoint_valuationSubring_twoChartModel_x1_mul
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
    (Mdl₂ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₂ : Mdl₂.C ≅ C₂)
    (he₂ : e₂.hom ≫ c₂ = Mdl₂.toBase)

    (θ₂ : G.JE ≃+ AlgebraicCurve.Pic0 k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hθpin₂ : ∀ (g : G.JE) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂),
      Nonempty ((hrep₂.some.poincare.pullbackAlong (ptsE g)).L ≅
        (RelEffCartierDiv.ofPoint c₂ x.1 x.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₂ ε₂.1 ε₂.2).idealModule) →
      ∃ Dv : Divisor.degZero (K := k) (F := ↥(ModularCurve.igusaFunctionFieldX1C k M w)),
        (Dv : Divisor k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) =
          Finsupp.single (Mdl₂.pointEquivPlace ⟨x.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact x.2⟩) 1 -
            Finsupp.single (Mdl₂.pointEquivPlace ⟨ε₂.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact ε₂.2⟩) 1 ∧
        θ₂ g = Pic0.mk Dv)

    (U : (ModularCurve.TwoChartModel A (↥K) j).Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j))]
    (hUmax : ∀ W : (ModularCurve.TwoChartModel A (↥K) j).Opens, SmoothOfRelativeDimension 1 (W.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j)) → W ≤ U)

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ)

    (hπk : Function.Surjective πk) :
    ∀ (ξ₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j)) (ξ₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j))
      (d₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂) (d₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂),
      Set.range ξ₁.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j)) → Set.range ξ₂.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j)) →
      d₁.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ ξ₁.1 →
      (d₁.1 ≫ i₂.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₁.1.base →
      d₂.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ ξ₂.1 →
      (d₂.1 ≫ i₂.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₁.1.base →
      ∀ (s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase),
        Nonempty ((hrep.some.poincare.pullbackAlong s).L ≅
          (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) ξ₁.1 ξ₁.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) ξ₂.1 ξ₂.2).idealModule) →
        ∀ (y : G.J0s),
          (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ s.1 →
          ∀ (Dbar : Divisor.degZero (K := k) (F := ↥(ModularCurve.igusaFunctionFieldX1C k M w))),
            (Dbar : Divisor k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) =
              Finsupp.single (Mdl₂.pointEquivPlace ⟨d₁.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact d₁.2⟩) 1 -
                Finsupp.single (Mdl₂.pointEquivPlace ⟨d₂.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact d₂.2⟩) 1 →
            θ₂ (G.proj y).2 = Pic0.mk Dbar := by sorry
