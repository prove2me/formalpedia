-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_finset_heckeDivOneBar_single_eq_single_add_sum_of_red_notMem_of_reducesSnd_of_gaussReading_snd_algEquiv_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_finset_heckeDivOneBar_single_eq_single_add_sum_of_red_notMem_of_reducesSnd_of_gaussReading_snd_algEquiv_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/44f06615-34f9-554d-a7f4-f8426d6ddd6e
-- title:
--   Sorting Uₚ at places reducing into the twisted component
-- statement:
--   The data fall into several groups.
--
--   **Arithmetic data.** A prime $p$; a natural number $M$ with $5 \le M$ (`hM`) and $p \nmid M$ (`hpM`); a field $L$ of characteristic zero that is a $\{p\}$-cyclotomic extension of $\mathbb{Q}$, and $\zeta \in L$ a primitive $p$-th root of unity (`hζ`). Next, an intermediate field $K$ of $L \subseteq L((q)) =$ `LaurentSeries L` with `hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`, that is, $K$ is generated over $L$ by the coefficientwise image under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of the $q$-expansion function field of $X_1(Mp)$ over $\mathbb{Q}$. Further, a discrete valuation domain $A$ with an $A$-algebra structure on $L$ making $L$ its fraction field, such that $p$ lies in the maximal ideal of $A$ (`hAp`) and $\zeta$ lies in the image of $A$ in $L$ (`hζA`), together with an $A$-algebra structure on $K$ compatible with that of $L$; and an element $j \in K$ whose Laurent series is the image under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular $j$-invariant (`hj`), with $j \ne 0$.
--
--   **The special fibre and its two components.** An algebraically closed field $k$ of characteristic $p$, an $A$-algebra; schemes $C_1, C_2$ with structure morphisms $c_1, c_2$ to $\operatorname{Spec} k$ which are proper, smooth of relative dimension $1$ and geometrically integral; and closed immersions $i_1, i_2$ of $C_1, C_2$ over $\operatorname{Spec} k$ into the base change to $k$ of the two-chart integral model [`ModularCurve.TwoChart.modelTo A ↥K j`](def/ModularCurve_TwoChartModel.html#L252) (the pushout of the two affine charts given by the subalgebras of elements of $K$ integral over $A[j]$, respectively over $A[j^{-1}]$). The hypothesis `hcover` says that every point of `pullback (ModularCurve.TwoChart.modelTo A ↥K j) (specMap A k)` lies in the image of $i_1$ or of $i_2$; `hred` says that the intersection `pullback i₁.1 i₂.1` is reduced; `hn` names its number of points $n$, and `hn0` requires $n > 0$. The model [`ModularCurve.TwoChart.modelTo A ↥K j`](def/ModularCurve_TwoChartModel.html#L252) is assumed proper.
--
--   **The generic fibre model.** With $\overline{\mathbb{Q}}$ an $A$-algebra and an $L$-algebra in a compatible tower, a curve model $M\eta$ over $\overline{\mathbb{Q}}$ of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) (a proper smooth integral curve over $\overline{\mathbb{Q}}$ with a fixed isomorphism `ffEquiv` of that field with its function field and a bijection from its closed points to places), an isomorphism $e\eta$ from $M\eta.C$ onto the $\overline{\mathbb{Q}}$-fibre of the two-chart model, compatible with the structure morphisms (`heη`), and a nonemptiness assumption for the preimage of the finite chart. The hypothesis `hMηpin` pins the identification of function fields generically: for every $a$ in the finite chart algebra [`ModularCurve.TwoChart.chartAlgFin A ↥K j`](def/ModularCurve_TwoChartModel.html#L135), the germ at the generic point of the pullback of $a$ along $e\eta$ followed by the first projection corresponds under `Mη.ffEquiv.symm` to the element of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) whose Laurent series is the coefficientwise image of the Laurent series of $a$ under $L \to \overline{\mathbb{Q}}$. The hypothesis `hgal` asserts Galois equivariance of `Mη.pointEquivPlace`: for every automorphism $g$ of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ fixing $L$ pointwise and any two $\overline{\mathbb{Q}}$-points $x, x'$ of $M\eta.C$ (sections of `Mη.toBase`), if $x'$ followed by $e\eta$ and the first projection equals $\operatorname{Spec}(g)$ followed by the corresponding composite for $x$, then `Mη.pointEquivPlace x'` is the translate of `Mη.pointEquivPlace x` by [`ModularCurve.arithmeticGalois (ModularCurve.x1FunctionField (M * p)) g`](def/ModularCurve_ArithmeticGalois.html#L54).
--
--   **The Igusa models of the two components.** An integral weight-one form $w$ on $\Gamma_1(M)$ over $k$ (a weight-one modular form together with an integral $q$-expansion power series whose reduction in $k$ is nonzero), giving the Igusa function field [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35), the subfield of $k((q))$ generated by [`ModularCurve.x1FunctionFieldC k M`](def/ModularCurve_X1.html#L134) and the inverse of that reduced series. A curve model $\mathrm{Mdl}_1$ over $k$ of this field together with an isomorphism $e_1 : \mathrm{Mdl}_1.C \cong C_1$ compatible with the structure morphisms (`he₁`), a nonemptiness assumption `hne₁` for the preimage of the finite chart, and the Gauss reading pin `hgauss₁`: for $a$ in the finite chart algebra and $x, y \in A[[q]]$ with the reduction of $y$ to $k[[q]]$ nonzero and $a \cdot y = x$ in $L((q))$, the germ of $a$ at the generic point of $\mathrm{Mdl}_1.C$, transported along $e_1$ followed by $i_1$ and the first projection, corresponds under $\mathrm{Mdl}_1.\mathrm{ffEquiv}^{-1}$ to the element of the Igusa field with Laurent series $\bar{x}/\bar{y}$.
--
--   **The twist.** An $L$-algebra automorphism $\sigma$ of $K$ with: `hσj`, the Laurent series of $\sigma j$ is the coefficientwise image of [`ModularCurve.qExpand ℚ p ModularCurve.jq`](def/ModularCurve_X0.html#L25), i.e. $j$ read in $q^p$; `hσfin`, $\sigma$ preserves the finite chart algebra in both directions; and `hσW`, for every valuation subring $W_0$ of $K$ consisting exactly of those $f$ admitting a presentation $f \cdot y = x$ with $x, y \in A[[q]]$ and $y$ of nonzero reduction, the $\sigma$-pullback of $W_0$ is different from $W_0$ and contains both $P(j)$ and $P(j)^{-1}$ for every polynomial $P$ over $A$ with nonzero reduction. Further, an automorphism $\bar{\sigma}$ of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) over $\overline{\mathbb{Q}}$ matching $\sigma$ under coefficientwise base change (`hσbar`). A second curve model $\mathrm{Mdl}_2$ over $k$ of the same Igusa function field with an isomorphism $e_2 : \mathrm{Mdl}_2.C \cong C_2$ compatible with the structure morphisms (`he₂`), a nonemptiness assumption `hne₂`, and the $\sigma$-twisted reading pin `hgauss₂`, which is the analogue of `hgauss₁` on $C_2$ with the presentation $\sigma(a) \cdot y = x$ in place of $a \cdot y = x$.
--
--   **Frobenius on the Igusa field.** An element $\mathrm{frobIg}$ of `SemilinearAut k (ModularCurve.igusaFunctionFieldX1C k M w)` (a pair consisting of a ring automorphism of the field and one of $k$, compatible with the structure map) acting on Laurent coefficients by $p$-th powers: for all $x$ and all $n \in \mathbb{Z}$, the $n$-th coefficient of $\mathrm{frobIg} \cdot x$ is the $p$-th power of the $n$-th coefficient of $x$ (`hfrobIg`).
--
--   **Reduction data.** A valuation subring $\mathrm{Pl}$ of $\overline{\mathbb{Q}}$ with $p$ in its nonunits (`hPl`); a ring homomorphism $\rho : A \to \mathrm{Pl}$ lifting $A \to \overline{\mathbb{Q}}$ (`hρ`); a subring $O$ of $\overline{\mathbb{Q}}$ with $O \le \mathrm{Pl}$ (`hO`) and, conversely, $\mathrm{Pl} \le O$ (`hOPl`); a lift $\rho_O : A \to O$ of $A \to \overline{\mathbb{Q}}$ (`hρO`); and a surjective (`hπk`) ring homomorphism $\pi_k : \mathrm{Pl} \to k$ with $A \to k$ equal to $\pi_k \circ \rho$ (`hAlgk`). Finally two maps $\mathrm{red}_1, \mathrm{red}_2$ from places of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) over $\overline{\mathbb{Q}}$ to places of the Igusa function field over $k$, pinned by `hred₁` and `hred₂` respectively: for a place $P$, a morphism $\xi : \operatorname{Spec} O \to$ two-chart model over $\operatorname{Spec}(\rho_O)$, and a $k$-point $c$ of $C_1$ (resp. $C_2$), if the restriction of $\xi$ along $\operatorname{Spec}$ of the inclusion $O \hookrightarrow \overline{\mathbb{Q}}$ is the $\overline{\mathbb{Q}}$-point `Mη.pointEquivPlace.symm P` followed by $e\eta$ and the first projection, and if $c$ followed by $i_1$ (resp. $i_2$) and the first projection is $\operatorname{Spec}$ of $\pi_k \circ (O \hookrightarrow \mathrm{Pl})$ followed by $\xi$, then $\mathrm{red}_1 P$ (resp. $\mathrm{red}_2 P$) is the place attached by $\mathrm{Mdl}_1.\mathrm{pointEquivPlace}$ (resp. $\mathrm{Mdl}_2$) to the point $c$ followed by $e_1^{-1}$ (resp. $e_2^{-1}$).
--
--   **Hecke data.** `hβdef` asserts [`ModularCurve.HeckeBetaOneDefined (M * p) p`](def/ModularCurve_X1HeckeOperator.html#L84), namely that [`ModularCurve.qExpand ℚ p`](def/ModularCurve_X0.html#L25) carries [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137) into [`ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)`](def/ModularCurve_X1.html#L142); `hα` and `hβ` assert that the two algebra maps `heckeAlphaOneBar` and `heckeBetaOneBar` over $\overline{\mathbb{Q}}$ at level $M p$ and prime $p$ are integral; a `HasPrincipalDivisors` instance is assumed for the base change to $\overline{\mathbb{Q}}$ of [`ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)`](def/ModularCurve_X1.html#L142); and `hdeg` asserts [`AlgebraicCurve.finrankAlong`](def/AlgebraicCurve_Correspondence.html#L51) of [`ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) (M * p) p`](def/ModularCurve_X1HeckeOperator.html#L116) equals $p$.
--
--   **Conclusion.** There is a finite set $S_0$ of places of [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35) over $k$ such that the following holds for every place $P$ of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) over $\overline{\mathbb{Q}}$.
--
--   Suppose first that $P$ reduces into $C_2$ off the intersection and inside the finite chart, in the following precise sense: there exist $\xi : \operatorname{Spec} O \to$ two-chart model over $\operatorname{Spec}(\rho_O)$ and a $k$-point $c$ of $C_2$ such that (i) the restriction of $\xi$ along $O \hookrightarrow \overline{\mathbb{Q}}$ is the $\overline{\mathbb{Q}}$-point of $P$ followed by $e\eta$ and the first projection; (ii) $c$ followed by $i_2$ and the first projection is $\operatorname{Spec}(\pi_k \circ (O \hookrightarrow \mathrm{Pl}))$ followed by $\xi$; (iii) no point of $\operatorname{Spec} k$ is sent by $c$ into the image of the second projection `pullback.snd i₁.1 i₂.1` (so the reduction avoids the intersection of the two components); and (iv) the image of $c$ followed by $i_2$ and the first projection lies in the image of the finite chart [`ModularCurve.TwoChart.ιFin A ↥K j`](def/ModularCurve_TwoChartModel.html#L231). Suppose moreover that $\mathrm{red}_2 P \notin S_0$.
--
--   Then there are a place $Q_p$ and a family $Q : \mathrm{Fin}(p-1) \to$ places of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) over $\overline{\mathbb{Q}}$ such that:
--
--   1.
--
--   [`ModularCurve.heckeDivOneBar hα hβ`](def/ModularCurve_X1HeckeOperator.html#L151) at level $M p$ and prime $p$ — the divisor correspondence obtained by pulling back along `heckeBetaOneBar` and pushing forward along `heckeAlphaOneBar` — applied to the divisor $\mathrm{single}\,P\,1$ equals $\mathrm{single}\,Q_p\,1 + \sum_{i : \mathrm{Fin}(p-1)} \mathrm{single}\,(Q\,i)\,1$;
--
--   2.
--
--   $Q_p$ satisfies the same four clauses (i)–(iv) as $P$: there exist $\xi$ and a $k$-point $c$ of $C_2$ with the restriction of $\xi$ equal to the $\overline{\mathbb{Q}}$-point of $Q_p$ followed by $e\eta$ and the first projection, with $c$ followed by $i_2$ and the first projection the reduction of $\xi$, with the image of $c$ avoiding the image of `pullback.snd i₁.1 i₂.1`, and with the image of $c$ followed by $i_2$ and the first projection inside the image of the finite chart;
--
--   3.
--
--   for every $i : \mathrm{Fin}(p-1)$ the place $Q\,i$ reduces into $C_1$ off the intersection and inside the finite chart: there exist $\xi$ and a $k$-point $c$ of $C_1$ with the restriction of $\xi$ equal to the $\overline{\mathbb{Q}}$-point of $Q\,i$ followed by $e\eta$ and the first projection, with $c$ followed by $i_1$ and the first projection equal to $\operatorname{Spec}(\pi_k \circ (O \hookrightarrow \mathrm{Pl}))$ followed by $\xi$, with no point of $\operatorname{Spec} k$ sent by $c$ into the image of the first projection `pullback.fst i₁.1 i₂.1`, and with the image of $c$ followed by $i_1$ and the first projection inside the image of the finite chart.
--
--   Thus, apart from places whose reduction lies in the fixed finite set $S_0$, the level-$p$ Hecke correspondence carries a place reducing into the $\sigma$-twisted component to one place again on that component together with $p-1$ places on the Gauss component, each with multiplicity one.
--
--   This is the sorting statement for the level-$p$ Hecke correspondence on the two-chart integral model of $X_1(Mp)$ over a discrete valuation ring containing $\zeta_p$: classically it expresses the canonical-subgroup dichotomy (the quotient of a point with étale $p$-structure by its canonical subgroup stays on the étale branch, while the remaining $p-1$ $p$-isogenous structures are multiplicative, hence lie on the Gauss branch). It is used in the determination of $U_p$ and of the diamond operators on the degree-zero Picard group of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_finset_heckeDivOneBar_single_eq_single_add_sum_of_red_notMem_of_reducesSnd_of_gaussReading_snd_algEquiv_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
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
set_option maxHeartbeats 400000 in

theorem ModularCurve.XOneP.exists_finset_heckeDivOneBar_single_eq_single_add_sum_of_red_notMem_of_reducesSnd_of_gaussReading_snd_algEquiv_twoChartModel_x1_mul
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

    [NeZero p]
    (σ : ↥K ≃ₐ[L] ↥K)
    (hσj : ((σ j : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq))
    (hσfin : ∀ b : ↥K, b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j ↔
        σ b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
    (hσW : ∀ W₀ : ValuationSubring ↥K,
        (∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
          (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
            = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) →
        W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ≠ W₀ ∧
        (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
          Polynomial.aeval j P ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ∧
          (Polynomial.aeval j P)⁻¹ ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom))

    (σbar : ↥(ModularCurve.x1FunctionFieldBar (M * p)) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar (M * p)))
    (hσbar : ∀ (f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) (b : ↥K),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥K) : LaurentSeries L) →
      ((σbar f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((σ b : ↥K) : LaurentSeries L))
    (Mdl₂ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₂ : Mdl₂.C ≅ C₂)
    (he₂ : e₂.hom ≫ c₂ = Mdl₂.toBase)

    [hne₂ : Nonempty (Scheme.Opens.toScheme ((e₂.hom ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hgauss₂ : ∀ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
      y.map (algebraMap A k) ≠ 0 →
      ((σ (a : ↥K) : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      ((Mdl₂.ffEquiv.symm
        (Mdl₂.C.germToFunctionField ((e₂.hom ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
          (((e₂.hom ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
            (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
        : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) =
      HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) / HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k)))

    (frobIg : SemilinearAut k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hfrobIg : ∀ (x : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (n : ℤ),
      ((frobIg • x : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k).coeff n = ((x : LaurentSeries k).coeff n) ^ p)

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
      red₁ P = Mdl₁.pointEquivPlace ⟨c.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact c.2⟩)

    (red₂ : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) →
      AlgebraicCurve.Place k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hred₂ : ∀ (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)))
        (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) (ModularCurve.TwoChart.modelTo A (↥K) j))
        (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂),
      Spec.map (CommRingCat.ofHom O.subtype) ≫ ξ.1 =
        (Mη.pointEquivPlace.symm P).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) →
      c.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
        Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ ξ.1 →
      red₂ P = Mdl₂.pointEquivPlace ⟨c.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact c.2⟩)

    (hOPl : Pl.toSubring ≤ O)

    (hβdef : ModularCurve.HeckeBetaOneDefined (M * p) p)
    (hα : ModularCurve.HeckeAlphaOneBarIntegral (AlgebraicClosure ℚ) (M * p) p)
    (hβ : ModularCurve.HeckeBetaOneBarIntegral (AlgebraicClosure ℚ) (M * p) p)
    [HasPrincipalDivisors (AlgebraicClosure ℚ)
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))]

    (hdeg : AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ) (ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) (M * p) p) = p) :
    ∃ S₀ : Finset (AlgebraicCurve.Place k ↥(ModularCurve.igusaFunctionFieldX1C k M w)),
    ∀ (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p))),
      (∃ (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) (ModularCurve.TwoChart.modelTo A (↥K) j))
         (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂),
        Spec.map (CommRingCat.ofHom O.subtype) ≫ ξ.1 =
          (Mη.pointEquivPlace.symm P).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ∧
        c.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
          Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ ξ.1 ∧
        (∀ t, c.1.base t ∉ Set.range (pullback.snd i₁.1 i₂.1).base) ∧
        ∀ t, (c.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base t ∈
          Set.range (ModularCurve.TwoChart.ιFin A (↥K) j).base) →
      red₂ P ∉ S₀ →
      ∃ (Qp : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p))) (Q : Fin (p - 1) → AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p))),
        ModularCurve.heckeDivOneBar (L := AlgebraicClosure ℚ) (M := M * p) (ℓ := p) hα hβ (Finsupp.single P 1) =
          Finsupp.single Qp 1 + ∑ i : Fin (p - 1), Finsupp.single (Q i) 1 ∧
        (∃ (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) (ModularCurve.TwoChart.modelTo A (↥K) j))
           (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂),
          Spec.map (CommRingCat.ofHom O.subtype) ≫ ξ.1 =
            (Mη.pointEquivPlace.symm Qp).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ∧
          c.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
            Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ ξ.1 ∧
          (∀ t, c.1.base t ∉ Set.range (pullback.snd i₁.1 i₂.1).base) ∧
          ∀ t, (c.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base t ∈
            Set.range (ModularCurve.TwoChart.ιFin A (↥K) j).base) ∧
        ∀ i : Fin (p - 1),
          (∃ (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) (ModularCurve.TwoChart.modelTo A (↥K) j))
             (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
            Spec.map (CommRingCat.ofHom O.subtype) ≫ ξ.1 =
              (Mη.pointEquivPlace.symm (Q i)).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ∧
            c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
              Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ ξ.1 ∧
            (∀ t, c.1.base t ∉ Set.range (pullback.fst i₁.1 i₂.1).base) ∧
            ∀ t, (c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base t ∈
              Set.range (ModularCurve.TwoChart.ιFin A (↥K) j).base) := by sorry
