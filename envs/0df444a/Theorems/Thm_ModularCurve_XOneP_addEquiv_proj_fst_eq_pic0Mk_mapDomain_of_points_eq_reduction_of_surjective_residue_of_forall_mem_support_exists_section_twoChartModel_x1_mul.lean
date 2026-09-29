-- Prove2me | Theorems.Thm_ModularCurve_XOneP_addEquiv_proj_fst_eq_pic0Mk_mapDomain_of_points_eq_reduction_of_surjective_residue_of_forall_mem_support_exists_section_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.addEquiv_proj_fst_eq_pic0Mk_mapDomain_of_points_eq_reduction_of_surjective_residue_of_forall_mem_support_exists_section_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/e9221772-d51d-5bdd-bfdc-44bcad6ec306
-- title:
--   Abel–Jacobi commutes with reduction onto the Igusa component
-- statement:
--   Setting. Fix a prime $p$ and an integer $M$ with $5 \le M$, $M \neq 0$ and $p \nmid M$. Let $L$ be a field of characteristic zero which is a $p$-cyclotomic extension of $\mathbb{Q}$, and $\zeta \in L$ a primitive $p$-th root of unity. Let $K$ be an intermediate field of $L \subseteq \operatorname{LaurentSeries} L$, required by `hK` to be [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield generated over $L$ by the coefficientwise image of the function field of $X_1(Mp)$ over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with fraction field $L$, with $p$ in its maximal ideal (`hAp`) and $\zeta$ in the image of $A$ (`hζA`), and let $K$ be an $A$-algebra compatibly with $L$. Let $j \in K$ be the element whose Laurent series is the image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) (`hj`), with $j \ne 0$; write $X =$ [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) for the two-chart integral model over $\operatorname{Spec} A$ attached to $j$, assumed proper.
--
--   Special fibre. Let $k$ be an algebraically closed $A$-algebra field of characteristic $p$. Let $c_1 : C_1 \to \operatorname{Spec} k$ and $c_2 : C_2 \to \operatorname{Spec} k$ be proper, smooth of relative dimension $1$ and geometrically integral, and let $i_1, i_2$ be closed immersions of $C_1, C_2$ into the base change of $X$ to $k$, compatibly with $c_1, c_2$. The hypothesis `hcover` states that every point of that base change lies in the image of $i_1$ or of $i_2$; `hred` states that the scheme-theoretic intersection `pullback i₁.1 i₂.1` is reduced, and `hn`, `hn0` that its number of points equals $n$ with $0 < n$.
--
--   Sections and relative $\operatorname{Pic}^0$. Let $\varepsilon$ be a section of $X \to \operatorname{Spec} A$, and $\varepsilon_1, \varepsilon_2$ sections of $c_1, c_2$, with `hε₁` asserting that $\varepsilon_1$ followed by $i_1$ is the base change of $\varepsilon$ to $k$. Let $D$ be a `RelativePic0Designation` for $X$ over $A$ (a scheme with a structure morphism `D.toBase` to $\operatorname{Spec} A$ and a zero section), with `hrep` asserting that $D$ represents the $\varepsilon$-rigidified relative Picard functor cut out by the fibrewise algebraic-equivalence-to-zero condition `algEquivZeroCut`, and with `hsm`, `hsep` asserting that `D.toBase` is smooth and separated. The hypothesis `hreps` asserts the analogous representability for the base change of $X$ and of $D$ to $k$, and `hPk` that the Poincaré bundle of `hreps` is isomorphic to the base change to $k$ of the pullback of the Poincaré bundle of `hrep.some` along `pullback.fst D.toBase (specMap A k)`. Let $D_1$, $D_2$ be designations for $c_1$, $c_2$ with representability hypotheses `hrep₁`, `hrep₂`. Let $\nu_2$ be a morphism from the base change of $D$ to $k$ to $D_2$ over $\operatorname{Spec} k$; the hypothesis `hν₂` says that for every $k$-scheme $t : T \to \operatorname{Spec} k$ and every $T$-point $a$ of the base-changed $D$, the Poincaré bundle of `hrep₂` pulled back along $a$ followed by $\nu_2$ is isomorphic to the $\varepsilon_2$-rigidification (in the sense of `Scheme.Modules.rigidify` with respect to `rigSection c₂ t ε₂` and `pullback.snd c₂ t`) of the pullback along `curveChange i₂.1 i₂.2 t` of the bundle obtained from `hreps.poincare` along $a$; thus $\nu_2$ is restriction of line bundles to $C_2$ on relative Picard schemes.
--
--   Geometric generic fibre. Assume $\operatorname{AlgebraicClosure} \mathbb{Q}$ is an $A$- and $L$-algebra, compatibly. Let $M_\eta$ be a `CurveModel` over $\operatorname{AlgebraicClosure} \mathbb{Q}$ for [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) (a proper integral curve, smooth of relative dimension $1$, with an identification of its function field and a bijection between its closed points and the places), and $e_\eta$ an isomorphism of $M_\eta.C$ with the fibre of $X$ over $\operatorname{AlgebraicClosure}\mathbb{Q}$, compatible with the structure morphisms (`heη`).
--
--   Dictionary for the special fibre. Let $G$ be a [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9): abelian groups `G.J0s`, `G.JI`, `G.JE`, a subgroup `G.torus` of `G.J0s`, and a surjective homomorphism `G.proj : G.J0s →+ G.JI × G.JE` with kernel `G.torus`. Bijections `pts`, `ptsI`, `ptsE` identify `G.J0s`, `G.JI`, `G.JE` with the $k$-points of the base change of $D$ to $k$, of $D_1$ and of $D_2$ respectively. The hypotheses `hadd`, `haddI`, `haddE` state that these bijections are compatible with addition in the sense that the Poincaré bundle pulled back along the point attached to a sum is isomorphic to the tensor product of the two pullbacks, and `hproj` states that for every $x$ in `G.J0s` the point attached to the first component of `G.proj x` is `pts x` followed by `RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some`, and the point attached to the second component is `pts x` followed by $\nu_2$.
--
--   Abel–Jacobi data over the generic point. A bijection `gpts` identifies [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186), i.e. $\operatorname{Pic}^0$ of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) over $\operatorname{AlgebraicClosure}\mathbb{Q}$, with the $\operatorname{AlgebraicClosure}\mathbb{Q}$-points of `D.toBase`, and `hgadd` states that `gpts` is additive for the relative group law on `D.toBase` coming from `hrep.some` and the group cut `algEquivZeroGroupCut`. Further data over $L$: `hDL` is representability after base change to $L$; `ajL` is a point of the base change of $D$ to $L$ parametrised by the base-changed curve, with `hajLε` saying that $\varepsilon$ composed with `ajL` is the zero section and `hajL` saying that for every field $K'$, every $t : \operatorname{Spec} K' \to \operatorname{Spec} L$ and every $t$-point $x$ of the base-changed curve, the Poincaré bundle of `hDL` pulled back along $x$ followed by `ajL` is isomorphic to the line bundle of the relative effective Cartier divisor of the point $x$ tensored with the ideal module of the divisor of the section $\varepsilon$; `hPL` is the analogue of `hPk` over $L$. A morphism `kL` between the fibres over $\operatorname{AlgebraicClosure}\mathbb{Q}$ and over $L$ satisfies the two compatibilities `hkL₁`, `hkL₂` with the projections. A morphism `ajbar : Mη.C ⟶ D.P` is required by `hajbar` to equal $e_\eta$ followed by `kL`, by `ajL` and by `pullback.fst D.toBase (specMap A L)`, and by `hajbar_over` to lie over $M_\eta$'s structure morphism. A point $\bar\varepsilon$ of $M_\eta.C$ is required by `hεbar` to correspond to $\varepsilon$ and by `hεbar_aj` to be sent to the zero section by `ajbar`. Finally `hpts_aj` states: for all points $x, s$ of $M_\eta.C$ over $\operatorname{AlgebraicClosure}\mathbb{Q}$ with $s$ corresponding to $\varepsilon$, there is a degree-zero divisor $D_v$ equal to $(\text{place of } x) - (\text{place of } s)$ whose class under `gpts` is $x$ followed by `ajbar`.
--
--   Igusa curve. Let $w$ be a [`ModularCurve.IntegralWeightOneForm k M`](def/ModularCurve_IgusaFunctionFieldX1.html#L16), that is a weight-one modular form on $\Gamma_1(M)$ together with an integral power series which is its $q$-expansion and whose associated constant in $k$ is nonzero. Let $\mathrm{Mdl}_1$ be a `CurveModel` over $k$ for the Igusa function field [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35), with an isomorphism $e_1 : \mathrm{Mdl}_1.C \cong C_1$ over $\operatorname{Spec} k$ (`he₁`). Let $\theta_1$ be an isomorphism of abelian groups from `G.JI` to $\operatorname{Pic}^0$ of the Igusa function field over $k$, pinned by `hθpin₁`: for every $g$ in `G.JI` and every $k$-point $x$ of $c_1$, if the Poincaré bundle of `hrep₁` pulled back along `ptsI g` is isomorphic to the line bundle of the point divisor of $x$ tensored with the ideal module of the divisor of $\varepsilon_1$, then $\theta_1 g$ is the class of the degree-zero divisor $(\text{place of } x) - (\text{place of } \varepsilon_1)$, the places being taken through $e_1^{-1}$ and $\mathrm{Mdl}_1$'s point-place bijection.
--
--   Place data. Let $\mathrm{Pl}$ be a valuation subring of $\operatorname{AlgebraicClosure}\mathbb{Q}$ with `Pl.LiesOverPrime p`, i.e. $p$ is a nonunit of $\mathrm{Pl}$, and $\rho : A \to \mathrm{Pl}$ a ring homomorphism inducing the structure map $A \to \operatorname{AlgebraicClosure}\mathbb{Q}$ (`hρ`). Let $O$ be a subring of $\operatorname{AlgebraicClosure}\mathbb{Q}$ contained in $\mathrm{Pl}$ (`hO`), with $\rho_O : A \to O$ inducing the same structure map (`hρO`). Let $\pi_k : \mathrm{Pl} \to k$ be a ring homomorphism with $\pi_k \circ \rho$ the structure map $A \to k$ (`hAlgk`), assumed surjective (`hπk`).
--
--   Reduction of places. Let $\mathrm{red}_1$ be a map from places of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) over $\operatorname{AlgebraicClosure}\mathbb{Q}$ to places of the Igusa function field over $k$, subject to `hred₁`: for every place $P$, every $O$-point $\xi$ of $X$ (a section over `Spec.map (CommRingCat.ofHom ρO)`) and every $k$-point $c$ of $c_1$, if $\xi$ restricted along $O \hookrightarrow \operatorname{AlgebraicClosure}\mathbb{Q}$ is the point of $X$ corresponding to $P$ through $M_\eta$'s point-place bijection and $e_\eta$, and if $c$, pushed into $X$ through $i_1$, is $\xi$ reduced along $\pi_k \circ (O \hookrightarrow \mathrm{Pl})$, then $\mathrm{red}_1 P$ is the place of $\mathrm{Mdl}_1$ attached to $c$ through $e_1^{-1}$.
--
--   Conclusion. Under all of the above, for every degree-zero divisor $D_v$ of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) over $\operatorname{AlgebraicClosure}\mathbb{Q}$ the following holds. Assume that for every place $P$ in the support of $D_v$ there exist an $O$-point $\xi$ of $X$ and a $k$-point $c$ of $c_1$ such that $\xi$ restricted along $O \hookrightarrow \operatorname{AlgebraicClosure}\mathbb{Q}$ is the point of $X$ corresponding to $P$, such that $c$ composed with $i_1$ and the first projection is $\xi$ reduced along $\pi_k \circ (O \hookrightarrow \mathrm{Pl})$, and such that no point of the image of $c$ lies in the image of `pullback.fst i₁.1 i₂.1`, i.e. $c$ avoids the $n$ points of $C_1 \cap C_2$. Then for every $O$-point $z$ of `D.toBase` whose restriction along $O \hookrightarrow \operatorname{AlgebraicClosure}\mathbb{Q}$ is `gpts (Pic0.mk Dv)`, for every $y$ in `G.J0s` such that the $k$-point `pts y`, followed by `pullback.fst D.toBase (specMap A k)`, is $z$ reduced along $\pi_k \circ (O \hookrightarrow \mathrm{Pl})$, and for every degree-zero divisor $\bar D$ of the Igusa function field over $k$ with $\bar D =$ `Finsupp.mapDomain red₁` applied to $D_v$, one has
--   $$\theta_1\bigl((G.\mathrm{proj}\, y)_1\bigr) = \mathrm{Pic}^0.\mathrm{mk}\, \bar D .$$
--
--   This is the statement that the Abel–Jacobi map commutes with reduction on the Igusa component of the special fibre at $p$ of $J_1(Mp)$: a degree-zero divisor whose support reduces away from the nodes of the special fibre has reduction class, read through the pinned isomorphism $\theta_1$ of the component group $G.\mathrm{JI}$ with $\operatorname{Pic}^0$ of the Igusa curve, equal to the class of the reduced divisor $(\mathrm{red}_1)_* D_v$. It is used by [`ModularCurve.XOneP.addEquiv_proj_fst_eq_natCast_smul_frob_inv_smul_of_pts_reduction_heckeGenOne_of_points_pic0Mk_valuationSubring_of_forall_mem_support_gaussReduces_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.addEquiv_proj_fst_eq_natCast_smul_frob_inv_smul_of_pts_reduction_heckeGenOne_of_points_pic0Mk_valuationSubring_of_forall_mem_support_gaussReduces_twoChartModel_x1_mul), which converts this into the Frobenius/Hecke formula on the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_addEquiv_proj_fst_eq_pic0Mk_mapDomain_of_points_eq_reduction_of_surjective_residue_of_forall_mem_support_exists_section_twoChartModel_x1_mul.lean

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

theorem ModularCurve.XOneP.addEquiv_proj_fst_eq_pic0Mk_mapDomain_of_points_eq_reduction_of_surjective_residue_of_forall_mem_support_exists_section_twoChartModel_x1_mul
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

    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
    (eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase)

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

    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))

    (hDL : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)
        (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)) (D.baseChange L))
    (ajL : SchemeHomOver (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (D.baseChange L).toBase)
    (kL : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L))
    (ajbar : Mη.C ⟶ D.P)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (hPL : Nonempty (hDL.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε L
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A L), pullback.condition⟩)).L))
    (hajLε : (sectionBaseChange L ε).1 ≫ ajL.1 = (D.baseChange L).zeroSection)
    (hajL : (∀ (K' : Type) [Field K'] (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of L))
        (x : SchemeHomOver t (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L)),
      Nonempty ((hDL.poincare.pullbackAlong
          ⟨x.1 ≫ ajL.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajL.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (t ≫ (sectionBaseChange L ε).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange L ε).2).trans
              (Category.comp_id t)))).idealModule)))
    (hkL₁ : kL ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)))
    (hkL₂ : kL ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ≫ specMap L (AlgebraicClosure ℚ))
    (hajbar : ajbar = eη ≫ kL ≫ ajL.1 ≫ pullback.fst D.toBase (specMap A L))
    (hajbar_over : ajbar ≫ D.toBase = Mη.toBase ≫ specMap A (AlgebraicClosure ℚ))
    (hεbar : εbar.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1)
    (hεbar_aj : εbar.1 ≫ ajbar = specMap A (AlgebraicClosure ℚ) ≫ D.zeroSection)
    (hpts_aj : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (gpts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))

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

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (O : Subring (AlgebraicClosure ℚ)) (hO : O ≤ Pl.toSubring)
    (ρO : A →+* ↥O) (hρO : O.subtype.comp ρO = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ)

    (hπk : Function.Surjective ⇑πk)

    (red₁ : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) →
      AlgebraicCurve.Place k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hred₁ : ∀ (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)))
        (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) (ModularCurve.TwoChart.modelTo A (↥K) j))
        (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
      Spec.map (CommRingCat.ofHom O.subtype) ≫ ξ.1 =
        (Mη.pointEquivPlace.symm P).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) →
      c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
        Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ ξ.1 →
      red₁ P = Mdl₁.pointEquivPlace ⟨c.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact c.2⟩) :
    ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p))),

      (∀ P ∈ (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))).support,
        ∃ (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) (ModularCurve.TwoChart.modelTo A (↥K) j))
          (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
          Spec.map (CommRingCat.ofHom O.subtype) ≫ ξ.1 =
            (Mη.pointEquivPlace.symm P).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ∧
          c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
            Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ ξ.1 ∧
          ∀ t, c.1.base t ∉ Set.range (pullback.fst i₁.1 i₂.1).base) →

      ∀ (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) D.toBase),
        (gpts (Pic0.mk Dv)).1 = Spec.map (CommRingCat.ofHom O.subtype) ≫ z.1 →

        ∀ (y : G.J0s),
          (pts y).1 ≫ pullback.fst D.toBase (specMap A k) =
            Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ z.1 →
          ∀ (Dbar : Divisor.degZero (K := k) (F := ↥(ModularCurve.igusaFunctionFieldX1C k M w))),
            (Dbar : Divisor k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) =
              Finsupp.mapDomain red₁ (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) →
            θ₁ (G.proj y).1 = Pic0.mk Dbar := by sorry
