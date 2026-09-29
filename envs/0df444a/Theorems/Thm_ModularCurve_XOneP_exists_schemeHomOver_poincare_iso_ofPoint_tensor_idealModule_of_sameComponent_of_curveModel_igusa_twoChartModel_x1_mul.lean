-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_schemeHomOver_poincare_iso_ofPoint_tensor_idealModule_of_sameComponent_of_curveModel_igusa_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_schemeHomOver_poincare_iso_ofPoint_tensor_idealModule_of_sameComponent_of_curveModel_igusa_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/974a020d-9625-5171-b4fc-5665b95b04dc
-- title:
--   The Pic⁰-point of 𝒪(u₁-u₂) for same-component sections
-- statement:
--   The setting is the two-chart model of $X_1(Mp)$ over a discrete valuation ring and its relative $\mathrm{Pic}^0$.
--
--   *Arithmetic base data.* A prime $p$, an integer $M$ with $5 \le M$ and $p \nmid M$, a field $L$ of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, an element $\zeta \in L$ which is a primitive $p$-th root of unity, and an intermediate field $K$ of $L((q)) =$ `LaurentSeries L` with $K =$ [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. $K$ is generated over $L$ by the image, under coefficientwise extension of scalars, of the $\mathbb{Q}$-rational function field of $X_1(Mp)$ inside $\mathbb{Q}((q))$. Further, $A$ is a discrete valuation domain with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A$, $K$ is an $A$-algebra compatibly with $L$, and $j \in K$ is an element whose image in $L((q))$ is the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular invariant, with $j \neq 0$. The scheme under consideration is the two-chart model with structure morphism [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) over $\operatorname{Spec} A$, assumed proper.
--
--   *Special fibre data.* $k$ is an algebraically closed $A$-algebra field of characteristic $p$. Two schemes $C_1, C_2$ with morphisms $c_1, c_2$ to $\operatorname{Spec} k$, each proper, smooth of relative dimension $1$ and geometrically integral, are given together with closed immersions $i_1, i_2$ of $C_1, C_2$ into the base change of the model to $k$, over $\operatorname{Spec} k$. The hypothesis `hcover` states that every point of $X \times_{\operatorname{Spec} A} \operatorname{Spec} k$ lies in the range of $i_1$ or of $i_2$; `hred` states that the fibre product of $i_1$ and $i_2$ is reduced, and `hn`, `hn0` say that its cardinality equals a natural number $n$ with $0 < n$. Sections $\varepsilon$ of the model over $\operatorname{Spec} A$, and $\varepsilon_1, \varepsilon_2$ of $c_1, c_2$ over $\operatorname{Spec} k$, are given, with `hε₁` asserting that $\varepsilon_1$ followed by $i_1$ is the base change of $\varepsilon$ to $k$.
--
--   *Relative Picard data.* $D$ is a `RelativePic0Designation` for the model, that is a scheme $D.P$ with a structure morphism `D.toBase` to $\operatorname{Spec} A$ and a zero section; `hrep` asserts that $D$ represents the functor of rigidified line bundles on the model satisfying the condition imposed by `algEquivZeroCut` (the predicate `FibrewiseAlgEquivZero`), with Poincaré bundle `hrep.some.poincare`, universal property and triviality along the zero section; `hsm` and `hsep` require `D.toBase` to be smooth and separated. The hypothesis `hreps` is the corresponding representability statement for the base change of the model and of $D$ to $k$, and `hPk` asserts that its Poincaré bundle is isomorphic to the base change to $k$ (via `BaseChange.ofR`) of the pullback of `hrep.some.poincare` along the first projection of $D.P \times_{\operatorname{Spec} A} \operatorname{Spec} k$. Likewise $D_1, D_2$ are designations for $c_1, c_2$ over $k$, with representability data `hrep₁`, `hrep₂`.
--
--   *Restriction to the second component.* $\nu_2$ is a morphism from $D$ base-changed to $k$ to $D_2$ over $\operatorname{Spec} k$, and `hν₂` states that for every $k$-scheme $t : T \to \operatorname{Spec} k$ and every $T$-point $a$ of $D_k$, the pullback of `hrep₂.some.poincare` along $a$ followed by $\nu_2$ is isomorphic to the `Scheme.Modules.rigidify` of the pullback, along `curveChange i₂`, of the pullback of the Poincaré bundle of `hreps` along $a$; thus $\nu_2$ induces restriction of line bundles along $i_2$.
--
--   *The model over $\overline{\mathbb{Q}}$ and its Galois compatibility.* With $A$ and $L$ mapping compatibly to $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, a curve model $M_\eta$ over $\overline{\mathbb{Q}}$ with function field [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) is given, together with an isomorphism $e_\eta$ from $M_\eta.C$ to the base change of the two-chart model to $\overline{\mathbb{Q}}$, compatible with the structure morphisms (`heη`). The hypothesis `Mη_chart_nonempty` says that the preimage in $M_\eta.C$ of the image of the finite chart [`ModularCurve.TwoChart.ιFin`](def/ModularCurve_TwoChartModel.html#L231) is nonempty, and `hMηpin` says that for every element $a$ of the finite chart algebra [`ModularCurve.TwoChart.chartAlgFin A K j`](def/ModularCurve_TwoChartModel.html#L135), the element of the function field obtained by transporting the germ of $a$ at the generic point through `Mη.ffEquiv.symm` has, as a Laurent series over $\overline{\mathbb{Q}}$, the $q$-expansion obtained from that of $a$ in $L((q))$ by applying $L \to \overline{\mathbb{Q}}$ coefficientwise. The hypothesis `hgal` requires that for every $\mathbb{Q}$-automorphism $g$ of $\overline{\mathbb{Q}}$ fixing the image of $L$ pointwise and all $\overline{\mathbb{Q}}$-points $x, x'$ of $M_\eta.C$, if $x'$ followed by $e_\eta$ and the first projection coincides with $\operatorname{Spec} g$ followed by the same datum for $x$, then the place of $x'$ under `Mη.pointEquivPlace` is the translate of that of $x$ by [`ModularCurve.arithmeticGalois`](def/ModularCurve_ArithmeticGalois.html#L54) applied to $g$.
--
--   *Néron special fibre group data.* $G$ is a [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9): abelian groups `G.J0s`, `G.JI`, `G.JE`, a subgroup `G.torus` of `G.J0s`, and a surjective homomorphism `G.proj : G.J0s →+ G.JI × G.JE` with kernel `G.torus`. Bijections `pts`, `ptsI`, `ptsE` identify `G.J0s`, `G.JI`, `G.JE` with the $k$-points of $D_k$, $D_1$, $D_2$ over $\operatorname{Spec} k$ respectively; `hadd`, `haddI`, `haddE` state that these bijections are additive up to isomorphism of the pullbacks of the respective Poincaré bundles (the bundle at a sum being isomorphic to the tensor product of the bundles at the summands); and `hproj` states that for each $x$, `ptsI` of the first component of `G.proj x` is the composite of `pts x` with the morphism `RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some`, while `ptsE` of the second component is the composite of `pts x` with $\nu_2$.
--
--   *Igusa identification of the components.* $w$ is an [`ModularCurve.IntegralWeightOneForm k M`](def/ModularCurve_IgusaFunctionFieldX1.html#L16) and $Mdl_1, Mdl_2$ are curve models over $k$ with function field [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35), together with isomorphisms $e_1 : Mdl_1.C \cong C_1$ and $e_2 : Mdl_2.C \cong C_2$ compatible with the structure morphisms (`he₁`, `he₂`).
--
--   *Abel–Jacobi data.* A bijection `gpts` identifies $\mathrm{Pic}^0$ of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) with the $\overline{\mathbb{Q}}$-points of `D.toBase` over $\operatorname{Spec} A$, and `hgadd` states that it is additive for the relative group law attached to `hrep.some`. Further given are: representability data `hDL` after base change to $L$; a morphism `ajL` from the base change of the model to $L$ to $D$ base-changed to $L$, over $\operatorname{Spec} L$; the canonical morphism `kL` from the base change of the model to $\overline{\mathbb{Q}}$ to its base change to $L$ (characterised by `hkL₁`, `hkL₂` on the two projections); a morphism `ajbar` from $M_\eta.C$ to $D.P$; and a $\overline{\mathbb{Q}}$-point `εbar` of $M_\eta.C$. The hypothesis `hPL` compares the Poincaré bundle of `hDL` with the base change to $L$ of the pullback of `hrep.some.poincare` along the first projection; `hajLε` says that the base-changed section $\varepsilon_L$ followed by `ajL` is the zero section of $D_L$; `hajL` says that for every field $K'$, every morphism $t : \operatorname{Spec} K' \to \operatorname{Spec} L$ and every $t$-point $x$ of the model over $L$, the pullback of the Poincaré bundle of `hDL` along $x$ followed by `ajL` is isomorphic to the `lineBundle` of `RelEffCartierDiv.ofPoint` at $x$ tensored with the `idealModule` of `RelEffCartierDiv.ofPoint` at $t$ followed by $\varepsilon_L$, i.e. to $\mathcal{O}(x) \otimes \mathcal{O}(\varepsilon)^{-1}$; `hajbar` defines `ajbar` as $e_\eta$ followed by `kL`, by `ajL` and by the first projection of $D_L$; `hajbar_over` records that `ajbar` lies over $\operatorname{Spec} A$ through $M_\eta$; `hεbar` and `hεbar_aj` say that `εbar` corresponds to $\varepsilon$ on the model and to the zero section of $D$ under `ajbar`; and `hpts_aj` says that for all $\overline{\mathbb{Q}}$-points $x, s$ of $M_\eta.C$ with $s$ corresponding to $\varepsilon$, there is a degree-zero divisor $D_v$ on [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) equal to $[\,\text{place of } x\,] - [\,\text{place of } s\,]$ whose class under `gpts` is the point $x$ followed by `ajbar`.
--
--   *The two sections and the same-component hypothesis.* $Pl$ is a valuation subring of $\overline{\mathbb{Q}}$ with `Pl.LiesOverPrime p`, that is $p$ lies in the nonunits of $Pl$; $\rho : A \to Pl$ is a ring homomorphism whose composite with the inclusion of $Pl$ is the structure map $A \to \overline{\mathbb{Q}}$; $\pi_k : Pl \to k$ is a surjective ring homomorphism with $\pi_k \circ \rho$ the structure map $A \to k$. Two $Pl$-sections $u_1, u_2$ of the two-chart model over $\operatorname{Spec}\rho$ are given, together with $k$-points $u_{\kappa 1}, u_{\kappa 2}$ of the base change of the model to $k$ which are their reductions: `huκ₁'`, `huκ₂'` identify their first projections with $\operatorname{Spec}\pi_k$ followed by $u_1$, $u_2$, and `huκ₁`, `huκ₂` say that their second projections are the identity of $\operatorname{Spec} k$. Finally `hsame` requires that the images of the closed point of $\operatorname{Spec} k$ under $u_{\kappa 1}$ and $u_{\kappa 2}$ either both lie in the range of $i_1$ and not in that of $i_2$, or both lie in the range of $i_2$ and not in that of $i_1$.
--
--   *Conclusion.* There exists a $Pl$-point $s$ of `D.toBase` over $\operatorname{Spec}\rho$, that is a morphism $s : \operatorname{Spec} Pl \to D.P$ with $s$ followed by `D.toBase` equal to $\operatorname{Spec}\rho$, such that both of the following hold.
--
--   First, the pullback of the Poincaré bundle `hrep.some.poincare` along $s$ is isomorphic to the tensor product of the `lineBundle` of `RelEffCartierDiv.ofPoint` at $u_1$ with the `idealModule` of `RelEffCartierDiv.ofPoint` at $u_2$; since for a section the divisor `ofPoint` is the kernel ideal of its graph, with `lineBundle` its inverse module and `idealModule` the module of the ideal itself, this says $\mathcal{P}|_s \cong \mathcal{O}(u_1) \otimes \mathcal{O}(u_2)^{-1}$ on the model base-changed to $Pl$.
--
--   Second, for every $y \in G.J0s$ such that the $k$-point `pts y` of $D_k$, composed with the first projection of $D.P \times_{\operatorname{Spec} A} \operatorname{Spec} k$, equals $\operatorname{Spec}\pi_k$ followed by $s$ (that is, `pts y` is the reduction of $s$), the pullback of the Poincaré bundle of `hreps` along `pts y` is isomorphic to the tensor product of the `lineBundle` of `RelEffCartierDiv.ofPoint` at $u_{\kappa 1}$ with the `idealModule` of `RelEffCartierDiv.ofPoint` at $u_{\kappa 2}$, i.e. to $\mathcal{O}(\bar u_1) \otimes \mathcal{O}(\bar u_2)^{-1}$ on the special fibre.
--
--   This is the statement that a pair of $Pl$-valued sections of the two-chart model of $X_1(Mp)$ whose reductions lie on one and the same geometric component of the special fibre, and off the other, gives rise to a $Pl$-point of the relative $\mathrm{Pic}^0$ classifying $\mathcal{O}(u_1) \otimes \mathcal{O}(u_2)^{-1}$, whose reduction classifies the corresponding difference of the reduced points. It is used in the study of the reduction at $p$ of divisor classes coming from the inertia group, where the class of a difference of two points specialising to the same component is shown to have trivial image under the projection to the components of the special fibre of the Néron model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_schemeHomOver_poincare_iso_ofPoint_tensor_idealModule_of_sameComponent_of_curveModel_igusa_twoChartModel_x1_mul.lean

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
import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.exists_schemeHomOver_poincare_iso_ofPoint_tensor_idealModule_of_sameComponent_of_curveModel_igusa_twoChartModel_x1_mul
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
    (Mdl₂ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₂ : Mdl₂.C ≅ C₂)
    (he₂ : e₂.hom ≫ c₂ = Mdl₂.toBase)

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

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ) (hπk : Function.Surjective πk)
    (u₁ u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (uκ₁ uκ₂ : Spec (CommRingCat.of k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))
    (huκ₁' : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom πk) ≫ u₁.1) (huκ₁ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
    (huκ₂' : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom πk) ≫ u₂.1) (huκ₂ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
    (hsame : (uκ₁.base (IsLocalRing.closedPoint k) ∈ Set.range i₁.1.base \ Set.range i₂.1.base ∧
               uκ₂.base (IsLocalRing.closedPoint k) ∈ Set.range i₁.1.base \ Set.range i₂.1.base) ∨
             (uκ₁.base (IsLocalRing.closedPoint k) ∈ Set.range i₂.1.base \ Set.range i₁.1.base ∧
               uκ₂.base (IsLocalRing.closedPoint k) ∈ Set.range i₂.1.base \ Set.range i₁.1.base)) :
    ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
      Nonempty ((hrep.some.poincare.pullbackAlong s).L ≅
        (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) u₁.1 u₁.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) u₂.1 u₂.2).idealModule) ∧
      ∀ y : G.J0s, (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ s.1 →
        Nonempty ((hreps.poincare.pullbackAlong (pts y)).L ≅
          (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) uκ₁ huκ₁).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) uκ₂ huκ₂).idealModule) := by sorry
