-- Prove2me | Theorems.Thm_ModularCurve_XOneP_reducesSnd_iff_gaussReduces_smul_of_gaussReading_algEquiv_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.reducesSnd_iff_gaussReduces_smul_of_gaussReading_algEquiv_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/7039d57c-6c8d-59ce-af9d-e5359bf3ef16
-- title:
--   Reduction into C₂ versus Gauss reduction of the σ̄-translate
-- statement:
--   Fix a prime $p$ and a natural number $M$ with $5 \le M$ and $p \nmid M$ (`hM`, `hpM`). Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ for the set $\{p\}$, and let $\zeta \in L$ be a primitive $p$-th root of unity. Let $K$ be an intermediate field of $L((q))$ over $L$ with `hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`, i.e. $K$ is generated over $L$ by the coefficientwise image of the $q$-expansion function field of $X_1(Mp)$ over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with $L$ as fraction field, such that $p$ lies in the maximal ideal of $A$ (`hAp`) and $\zeta$ is in the image of $A$ in $L$ (`hζA`), and let $K$ be an $A$-algebra compatibly with the tower $A \to L \to K$. Let $j \in K$ have $q$-expansion the coefficientwise image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular invariant (`hj`). The relevant model is [`ModularCurve.TwoChartModel A K j`](def/ModularCurve_TwoChartModel.html#L229), obtained by glueing $\mathrm{Spec}$ of the subalgebra [`ModularCurve.TwoChart.chartAlgFin A K j`](def/ModularCurve_TwoChartModel.html#L135) of elements of $K$ integral over $A[j]$ to $\mathrm{Spec}$ of the subalgebra of elements integral over $A[j^{-1}]$ along the middle ring, with structure morphism [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) to $\mathrm{Spec}\,A$, assumed proper.
--
--   Geometric special fibre. Let $k$ be an algebraically closed field of characteristic $p$ which is an $A$-algebra, and let $c_1 : C_1 \to \mathrm{Spec}\,k$ and $c_2 : C_2 \to \mathrm{Spec}\,k$ be proper, smooth of relative dimension $1$ and geometrically integral. Let $i_1, i_2$ be closed immersions of $C_1$, $C_2$ into the base change of the two-chart model to $k$ (the pullback of `modelTo` along $\mathrm{Spec}\,k \to \mathrm{Spec}\,A$), each compatible with $c_1$, resp. $c_2$, over $\mathrm{Spec}\,k$. The hypothesis `hcover` says that every point of that pullback lies in the image of $i_1$ or of $i_2$; `hred` says that the scheme `pullback i₁.1 i₂.1` is reduced, and `hn`, `hn0` say that its number of points is $n$ with $0 < n$.
--
--   Generic fibre model. Let $M\eta$ be a `CurveModel` over $\overline{\mathbb{Q}}$ of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) $=$ `laurentBaseChange (AlgebraicClosure ℚ) (x1FunctionField (M * p))`: a proper smooth integral curve $M\eta.C$ over $\overline{\mathbb{Q}}$ together with an identification $M\eta.\mathrm{ffEquiv}$ of that field with its function field, compatible with the base field, and a bijection between closed points and places. Here $\overline{\mathbb{Q}}$ carries compatible $A$- and $L$-algebra structures. Let $e\eta$ be an isomorphism from $M\eta.C$ to the pullback of `modelTo` along $\mathrm{Spec}\,\overline{\mathbb{Q}} \to \mathrm{Spec}\,A$ with $e\eta$ followed by `pullback.snd` equal to $M\eta.\mathrm{toBase}$ (`heη`); the preimage under $e\eta$ followed by `pullback.fst` of the image of the finite chart [`ModularCurve.TwoChart.ιFin A K j`](def/ModularCurve_TwoChartModel.html#L231) is assumed non-empty. The reading hypothesis `hMηpin` states that for every $a$ in `chartAlgFin A K j` the element of `x1FunctionFieldBar (M * p)` obtained by transporting, along $M\eta.\mathrm{ffEquiv}^{-1}$, the germ at the generic point of the section of $a$ pulled back along $e\eta$ followed by `pullback.fst` has $q$-expansion the coefficientwise image under $L \to \overline{\mathbb{Q}}$ of the $q$-expansion of $a$. The Galois hypothesis `hgal` states that for every $\mathbb{Q}$-algebra automorphism $g$ of $\overline{\mathbb{Q}}$ fixing the image of $L$ pointwise, and all $\overline{\mathbb{Q}}$-points $x, x'$ of $M\eta.C$ (sections of $M\eta.\mathrm{toBase}$), if $x'$ followed by $e\eta$ followed by `pullback.fst` equals $\mathrm{Spec}(g)$ followed by $x$ followed by $e\eta$ followed by `pullback.fst`, then $M\eta.\mathrm{pointEquivPlace}\,x'$ is the translate of $M\eta.\mathrm{pointEquivPlace}\,x$ by [`ModularCurve.arithmeticGalois (x1FunctionField (M * p)) g`](def/ModularCurve_ArithmeticGalois.html#L54), the semilinear automorphism acting coefficientwise by $g$ on Laurent series.
--
--   Igusa reading of $C_1$. Let $w$ be a [`ModularCurve.IntegralWeightOneForm k M`](def/ModularCurve_IgusaFunctionFieldX1.html#L16), that is, a weight one modular form on $\Gamma_1(M)$ together with an integral power series realising its $q$-expansion whose image in $k$ is non-zero. Let $Mdl_1$ be a `CurveModel` over $k$ of [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35), the field obtained from the $q$-expansion function field of $X_1(M)$ over $k$ by adjoining the inverse of that image, and let $e_1 : Mdl_1.C \cong C_1$ satisfy $e_1.\mathrm{hom}$ followed by $c_1$ equal to $Mdl_1.\mathrm{toBase}$ (`he₁`); the corresponding chart preimage in $Mdl_1.C$ is assumed non-empty (`hne₁`). The Gauss reading pin `hgauss₁` states: for every $a$ in `chartAlgFin A K j` and all power series $x, y$ over $A$ with $y$ reducing to a non-zero series over $k$, if the $q$-expansion of $a$ times the image of $y$ over $L$ equals the image of $x$ over $L$, then the element of `igusaFunctionFieldX1C k M w` obtained from $a$ by the germ construction along $e_1.\mathrm{hom}$ followed by $i_1$ followed by `pullback.fst` has Laurent expansion the quotient of the reduction of $x$ by the reduction of $y$ over $k$.
--
--   The involution and its companions. Let $\sigma$ be an $L$-algebra automorphism of $K$ with: `hσj`, the $q$-expansion of $\sigma j$ is the coefficientwise image of [`ModularCurve.qExpand ℚ p ModularCurve.jq`](def/ModularCurve_X0.html#L25), i.e. $j$ in the variable $q^p$; `hσfin`, for every $b \in K$ one has $b \in$ `chartAlgFin A K j` if and only if $\sigma b \in$ `chartAlgFin A K j`; and `hσW`, for every valuation subring $W_0$ of $K$ whose members are exactly the $f$ admitting power series $x, y$ over $A$ with $y$ of non-zero reduction and $f$ times the image of $y$ equal to the image of $x$ over $L$, the pullback $W_0^{\,\sigma}$ of $W_0$ along $\sigma$ is different from $W_0$, and for every polynomial $P$ over $A$ with non-zero reduction both $P(j)$ and $P(j)^{-1}$ lie in $W_0^{\,\sigma}$. Let $\bar\sigma$ be an $\overline{\mathbb{Q}}$-algebra automorphism of `x1FunctionFieldBar (M * p)` compatible with $\sigma$ on $q$-expansions (`hσbar`: whenever $f$ has expansion the coefficientwise image of the expansion of $b \in K$, then $\bar\sigma f$ has expansion the coefficientwise image of the expansion of $\sigma b$). Let `frobIg` be a semilinear automorphism of `igusaFunctionFieldX1C k M w` over $k$ (a pair of ring automorphisms compatible with the structure map) acting on every Laurent coefficient by $x \mapsto x^p$ (`hfrobIg`).
--
--   Reduction apparatus. Let $Pl$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $Pl$ (`hPl`), let $\rho : A \to Pl$ lift the structure map $A \to \overline{\mathbb{Q}}$ (`hρ`), let $O$ be a subring of $\overline{\mathbb{Q}}$ with $O \le Pl$ (`hO`) and $Pl \le O$ (`hOPl`), let $\rho_O : A \to O$ lift the structure map (`hρO`), and let $\pi_k : Pl \to k$ be a surjective ring homomorphism (`hπk`) with $A \to k$ equal to $\pi_k \circ \rho$ (`hAlgk`). Let `red₁` be a map from places of `x1FunctionFieldBar (M * p)` over $\overline{\mathbb{Q}}$ to places of `igusaFunctionFieldX1C k M w` over $k$, pinned by `hred₁`: for every such place $P$, every $\xi : \mathrm{Spec}\,O \to$ `TwoChartModel A K j` over $\mathrm{Spec}(\rho_O)$ and every section $c$ of $c_1$, if $\mathrm{Spec}$ of the inclusion $O \hookrightarrow \overline{\mathbb{Q}}$ followed by $\xi$ equals the point $M\eta.\mathrm{pointEquivPlace}^{-1}(P)$ followed by $e\eta$ followed by `pullback.fst`, and $c$ followed by $i_1$ followed by `pullback.fst` equals $\mathrm{Spec}(\pi_k \circ (O \hookrightarrow Pl))$ followed by $\xi$, then `red₁ P` is the place of $Mdl_1$ attached to the point $c$ followed by $e_1.\mathrm{inv}$.
--
--   Hecke hypotheses. `hβdef` asserts [`ModularCurve.HeckeBetaOneDefined (M * p) p`](def/ModularCurve_X1HeckeOperator.html#L84), i.e. $q \mapsto q^p$ carries the function field of $X_1(Mp)$ into `x1x0FunctionFieldC ℚ (M * p) (M * p * p)`; `hα` and `hβ` assert that the ring homomorphisms underlying the degeneracy maps `heckeAlphaOneBar` and `heckeBetaOneBar` over $\overline{\mathbb{Q}}$ at level $Mp$ and prime $p$ are integral; the base-changed field `laurentBaseChange (AlgebraicClosure ℚ) (x1x0FunctionFieldC ℚ (M * p) (M * p * p))` is assumed to have principal divisors (every non-zero element has a degree-zero divisor recording its orders at all places); and `hdeg` asserts that the degree `finrankAlong` of `heckeBetaOneBar (AlgebraicClosure ℚ) (M * p) p` equals $p$.
--
--   Conclusion. For all places $P$ and $P_1$ of `x1FunctionFieldBar (M * p)` over $\overline{\mathbb{Q}}$ such that $P_1$ is the translate of $P$ by the semilinear automorphism `SemilinearAut.ofAlgAut σbar` attached to $\bar\sigma$, the following two assertions are equivalent.
--
--   First: there exist $\xi : \mathrm{Spec}\,O \to$ `TwoChartModel A K j` over $\mathrm{Spec}(\rho_O)$ and a section $c$ of $c_2$ such that (i) $\mathrm{Spec}$ of the inclusion $O \hookrightarrow \overline{\mathbb{Q}}$ followed by $\xi$ equals the point $M\eta.\mathrm{pointEquivPlace}^{-1}(P)$ followed by $e\eta$ followed by `pullback.fst`; (ii) $c$ followed by $i_2$ followed by `pullback.fst` equals $\mathrm{Spec}(\pi_k \circ (O \hookrightarrow Pl))$ followed by $\xi$; (iii) the image of $c$ on points avoids the range of the base map of `pullback.snd i₁.1 i₂.1`; and (iv) the image on points of $c$ followed by $i_2$ followed by `pullback.fst` lies in the range of the base map of the finite chart [`ModularCurve.TwoChart.ιFin A K j`](def/ModularCurve_TwoChartModel.html#L231).
--
--   Second: there exist $\xi : \mathrm{Spec}\,O \to$ `TwoChartModel A K j` over $\mathrm{Spec}(\rho_O)$ and a section $c$ of $c_1$ such that (i) $\mathrm{Spec}$ of the inclusion $O \hookrightarrow \overline{\mathbb{Q}}$ followed by $\xi$ equals the point $M\eta.\mathrm{pointEquivPlace}^{-1}(P_1)$ followed by $e\eta$ followed by `pullback.fst`; (ii) $c$ followed by $i_1$ followed by `pullback.fst` equals $\mathrm{Spec}(\pi_k \circ (O \hookrightarrow Pl))$ followed by $\xi$; (iii) the image of $c$ on points avoids the range of the base map of `pullback.fst i₁.1 i₂.1`; and (iv) the image on points of $c$ followed by $i_1$ followed by `pullback.fst` lies in the range of the base map of [`ModularCurve.TwoChart.ιFin A K j`](def/ModularCurve_TwoChartModel.html#L231).
--
--   At the level of individual places of $\overline{\mathbb{Q}}(X_1(Mp))$, this is the statement that the level-$p$ involution exchanges the two components of the geometric special fibre at $p$: a place reduces into $C_2$, away from the intersection with $C_1$ and inside the $j$-finite chart, exactly when its $\bar\sigma$-translate reduces in the same manner into the component $C_1$ carrying the Igusa (Gauss) reading. It is used in the subsequent sorting of places by component, where reductions are compared with the Frobenius and diamond actions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_reducesSnd_iff_gaussReduces_smul_of_gaussReading_algEquiv_twoChartModel_x1_mul.lean

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

theorem ModularCurve.XOneP.reducesSnd_iff_gaussReduces_smul_of_gaussReading_algEquiv_twoChartModel_x1_mul
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

    (hOPl : Pl.toSubring ≤ O)

    (hβdef : ModularCurve.HeckeBetaOneDefined (M * p) p)
    (hα : ModularCurve.HeckeAlphaOneBarIntegral (AlgebraicClosure ℚ) (M * p) p)
    (hβ : ModularCurve.HeckeBetaOneBarIntegral (AlgebraicClosure ℚ) (M * p) p)
    [HasPrincipalDivisors (AlgebraicClosure ℚ)
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))]

    (hdeg : AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ) (ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) (M * p) p) = p) :
    ∀ (P P₁ : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p))),
      P₁ = SemilinearAut.ofAlgAut σbar • P →
      ((∃ (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) (ModularCurve.TwoChart.modelTo A (↥K) j))
          (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂),
         Spec.map (CommRingCat.ofHom O.subtype) ≫ ξ.1 =
           (Mη.pointEquivPlace.symm P).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ∧
         c.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
           Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ ξ.1 ∧
         (∀ t, c.1.base t ∉ Set.range (pullback.snd i₁.1 i₂.1).base) ∧
         ∀ t, (c.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base t ∈
           Set.range (ModularCurve.TwoChart.ιFin A (↥K) j).base) ↔
       (∃ (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) (ModularCurve.TwoChart.modelTo A (↥K) j))
          (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
         Spec.map (CommRingCat.ofHom O.subtype) ≫ ξ.1 =
           (Mη.pointEquivPlace.symm P₁).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ∧
         c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
           Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ ξ.1 ∧
         (∀ t, c.1.base t ∉ Set.range (pullback.fst i₁.1 i₂.1).base) ∧
         ∀ t, (c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base t ∈
           Set.range (ModularCurve.TwoChart.ιFin A (↥K) j).base)) := by sorry
