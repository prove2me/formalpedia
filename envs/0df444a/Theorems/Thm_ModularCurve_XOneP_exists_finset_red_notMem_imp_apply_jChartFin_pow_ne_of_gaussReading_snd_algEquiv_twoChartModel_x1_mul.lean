-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_finset_red_notMem_imp_apply_jChartFin_pow_ne_of_gaussReading_snd_algEquiv_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_finset_red_notMem_imp_apply_jChartFin_pow_ne_of_gaussReading_snd_algEquiv_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/3f312bcb-c82c-5c48-a275-09aaa6a2f5ff
-- title:
--   Readings of j outside 𝔽_{p²} off finitely many places
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $5 \le M$ and $p \nmid M$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $\{p\}$, and let $\zeta \in L$ be a primitive $p$-th root of unity. Let $K$ be an intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ with $K =$ [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), that is, the subfield generated over $L$ by the coefficientwise image of the $q$-expansion function field of $X_1(Mp)$ over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A$, and let $K$ carry a compatible $A$-algebra structure (scalar tower $A \to L \to K$). Let $j \in K$ be nonzero with Laurent expansion [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81), the $q$-expansion of the modular function $j$ pushed into $\mathrm{LaurentSeries}\,L$. Throughout, [`ModularCurve.TwoChart.chartAlgFin A ↥K j`](def/ModularCurve_TwoChartModel.html#L135) denotes the subalgebra of elements of $K$ integral over $A[j]$, [`ModularCurve.TwoChart.jChartFin A ↥K j`](def/ModularCurve_TwoChartModel.html#L141) is $j$ regarded as an element of it, [`ModularCurve.TwoChart.ιFin A ↥K j`](def/ModularCurve_TwoChartModel.html#L231) is the finite-chart morphism from the spectrum of that subalgebra into the two-chart model, and [`ModularCurve.TwoChart.modelTo A ↥K j`](def/ModularCurve_TwoChartModel.html#L252) is the structure morphism of the two-chart model over $\operatorname{Spec} A$, which is assumed proper.
--
--   Let $k$ be an algebraically closed field of characteristic $p$ and an $A$-algebra. Let $C_1, C_2$ be schemes with morphisms $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$ that are proper, smooth of relative dimension $1$ and geometrically integral, and let $i_1, i_2$ be morphisms from $C_1$, $C_2$ to the base change of the two-chart model along $A \to k$, compatible with the structure morphisms, whose underlying scheme morphisms are closed immersions. The hypothesis `hcover` requires that every point of the base change $\mathrm{pullback}$ of [`ModularCurve.TwoChart.modelTo A ↥K j`](def/ModularCurve_TwoChartModel.html#L252) along $\operatorname{Spec} k \to \operatorname{Spec} A$ lie in the range of $i_1$ or of $i_2$; `hred` requires the scheme-theoretic intersection $\mathrm{pullback}\,i_1\,i_2$ to be reduced, and $n$ is a natural number with `Nat.card` of that intersection equal to $n$ and $0 < n$.
--
--   On the generic side, let there be $A$- and $L$-algebra structures on $\overline{\mathbb{Q}}$ forming a scalar tower, and let $M_\eta$ be a curve model over $\overline{\mathbb{Q}}$ of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182): an integral scheme, proper and smooth of relative dimension $1$ over $\operatorname{Spec} \overline{\mathbb{Q}}$, together with a ring isomorphism of that function field with the field of rational functions of the scheme compatible with the base field, and a bijection between closed points and places with the prescribed stalk-range property and the property that every finite set of points lies in an affine open. Let $e_\eta : M_\eta.C \to \mathrm{pullback}(\mathrm{modelTo}, \operatorname{Spec}(A \to \overline{\mathbb{Q}}))$ be an isomorphism with $e_\eta$ followed by the second projection equal to $M_\eta.\mathrm{toBase}$, and assume the preimage under $e_\eta$ followed by the first projection of the image of the finite chart is nonempty. The hypothesis `hMηpin` pins this identification: for every $a$ in the finite-chart subalgebra, the rational function on $M_\eta.C$ obtained by restricting $a$ along $e_\eta$ followed by the first projection and taking its germ at the generic point, transported back by $M_\eta.\mathrm{ffEquiv}^{-1}$, has Laurent expansion equal to the coefficientwise image along $L \to \overline{\mathbb{Q}}$ of the Laurent expansion of $a$. The hypothesis `hgal` requires Galois equivariance: for every automorphism $g$ of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ fixing the image of $L$ pointwise, and all $\overline{\mathbb{Q}}$-points $x, x'$ of $M_\eta.C$ (sections of $M_\eta.\mathrm{toBase}$), if $x'$ followed by $e_\eta$ followed by the first projection equals $\operatorname{Spec}(g)$ followed by $x$ followed by $e_\eta$ followed by the first projection, then the place attached to $x'$ is the image of the place attached to $x$ under the action of $g$ through [`ModularCurve.arithmeticGalois`](def/ModularCurve_ArithmeticGalois.html#L54) for [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137).
--
--   Let $w$ be an integral weight one form for $\Gamma_1(M)$ over $k$: a weight one modular form on $\Gamma_1(M)$ together with an integral power series which is its $q$-expansion and whose image in $\mathrm{LaurentSeries}\,k$ is nonzero.
--
--   Let $\sigma : K \simeq_L K$ be an $L$-algebra automorphism subject to three hypotheses. `hσj` requires the Laurent expansion of $\sigma j$ to be [`ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq)`](def/ModularCurve_LaurentCoeff.html#L81), the $q$-expansion of $j$ with $q$ replaced by $q^p$. `hσfin` requires, for every $b \in K$, that $b$ lie in the finite-chart subalgebra (in its [`AlgebraicCurve.TwoChartIntegralModel.chartAlgFin`](def/AlgebraicCurve_TwoChartIntegralModel.html#L142) form, defined by the same recipe) if and only if $\sigma b$ does. `hσW` requires, for every valuation subring $W_0$ of $K$ whose members are exactly those $f$ whose Laurent expansion can be written as a quotient $x/y$ of power series over $A$ with the reduction of $y$ nonzero, that the preimage of $W_0$ under $\sigma$ differ from $W_0$, and that for every polynomial $P$ over $A$ with nonzero reduction both $P(j)$ and $P(j)^{-1}$ lie in that preimage.
--
--   On the special fibre, let $\mathrm{Mdl}_2$ be a curve model over $k$ of [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35) (the field obtained from the $q$-expansion function field of $X_1(M)$ over $k$ by adjoining the inverse of the reduced $q$-expansion of $w$), with an isomorphism $e_2 : \mathrm{Mdl}_2.C \cong C_2$ such that $e_2$ followed by $c_2$ equals $\mathrm{Mdl}_2.\mathrm{toBase}$, and assume the preimage of the image of the finite chart under $e_2$ followed by $i_2$ followed by the first projection is nonempty. The hypothesis `hgauss₂` fixes the reading of the finite chart on $\mathrm{Mdl}_2$ as the $\sigma$-twisted one: for every $a$ in the finite-chart subalgebra and all power series $x, y$ over $A$ with the image of $y$ in $\mathrm{LaurentSeries}\,k$ nonzero, if the Laurent expansion of $\sigma a$ times the image of $y$ equals the image of $x$ over $L$, then the rational function on $\mathrm{Mdl}_2.C$ obtained from $a$ along $e_2$ followed by $i_2$ followed by the first projection has Laurent expansion over $k$ equal to the image of $x$ divided by the image of $y$.
--
--   Finally, let $\mathrm{Pl}$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit in it, let $\rho : A \to \mathrm{Pl}$ be a ring homomorphism whose composite with the inclusion is $A \to \overline{\mathbb{Q}}$, let $O$ be a subring of $\overline{\mathbb{Q}}$ contained in $\mathrm{Pl}$ with $\rho_O : A \to O$ likewise compatible, and let $\pi_k : \mathrm{Pl} \to k$ be a surjective ring homomorphism with $A \to k$ equal to $\pi_k \circ \rho$. Let $\mathrm{red}_2$ be a map from places of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) over $\overline{\mathbb{Q}}$ to places of [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35) over $k$, and let `hred₂` require: for every such place $P$, every morphism $\xi$ from $\operatorname{Spec} O$ to the two-chart model over $\operatorname{Spec}(\rho_O)$, and every $k$-point $c$ of $C_2$ over the identity, if $\operatorname{Spec}(O \hookrightarrow \overline{\mathbb{Q}})$ followed by $\xi$ equals the $\overline{\mathbb{Q}}$-point corresponding to $P$ followed by $e_\eta$ followed by the first projection, and $c$ followed by $i_2$ followed by the first projection equals $\operatorname{Spec}(\pi_k \circ (O \hookrightarrow \mathrm{Pl}))$ followed by $\xi$, then $\mathrm{red}_2(P)$ is the place attached by $\mathrm{Mdl}_2$ to the point $c$ followed by $e_2^{-1}$.
--
--   Under these hypotheses there exists a finite set $S_0$ of places of [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35) over $k$ with the following property. For every place $P$ of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) over $\overline{\mathbb{Q}}$, every ring homomorphism $\psi$ from the finite-chart subalgebra [`ModularCurve.TwoChart.chartAlgFin A ↥K j`](def/ModularCurve_TwoChartModel.html#L135) to $O$, and every $k$-point $c$ of $C_2$ over the identity of $\operatorname{Spec} k$, if
--
--   $\operatorname{Spec}(O \hookrightarrow \overline{\mathbb{Q}})$ followed by $\operatorname{Spec}(\psi)$ followed by [`ModularCurve.TwoChart.ιFin A ↥K j`](def/ModularCurve_TwoChartModel.html#L231) equals the $\overline{\mathbb{Q}}$-point corresponding to $P$ followed by $e_\eta$ followed by the first projection, and
--
--   $c$ followed by $i_2$ followed by the first projection equals $\operatorname{Spec}$ of $(\pi_k \circ (O \hookrightarrow \mathrm{Pl})) \circ \psi$ followed by [`ModularCurve.TwoChart.ιFin A ↥K j`](def/ModularCurve_TwoChartModel.html#L231), and
--
--   $\mathrm{red}_2(P) \notin S_0$,
--
--   then, writing $\chi := (\pi_k \circ (O \hookrightarrow \mathrm{Pl})) \circ \psi$ for the resulting character of the finite-chart subalgebra with values in $k$,
--   $$\chi(j)^{p^2} \ne \chi(j),$$
--   where $j$ is taken as [`ModularCurve.TwoChart.jChartFin A ↥K j`](def/ModularCurve_TwoChartModel.html#L141); equivalently, the reduced value of $j$ at such a point does not lie in $\mathbb{F}_{p^2}$.
--
--   This is the exceptional-set step in the comparison of places of $X_1(Mp)$ in characteristic $p$ with the Igusa cover of $X_1(M)$: away from a finite set of places of the Igusa function field (the poles of the $\sigma$-twisted reading of $j$ together with the places where its value lies in $\mathbb{F}_{p^2}$), a place whose $\overline{\mathbb{Q}}$-point extends to a finite-chart $O$-point reducing into the second branch has $j$-value outside $\mathbb{F}_{p^2}$. It is used by [`ModularCurve.XOneP.exists_finset_heckeDivOneBar_single_eq_single_add_sum_of_red_notMem_of_reducesSnd_of_gaussReading_snd_algEquiv_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_finset_heckeDivOneBar_single_eq_single_add_sum_of_red_notMem_of_reducesSnd_of_gaussReading_snd_algEquiv_twoChartModel_x1_mul) in the computation of Hecke divisors on $X_1(Mp)$ in characteristic $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_finset_red_notMem_imp_apply_jChartFin_pow_ne_of_gaussReading_snd_algEquiv_twoChartModel_x1_mul.lean

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

theorem ModularCurve.XOneP.exists_finset_red_notMem_imp_apply_jChartFin_pow_ne_of_gaussReading_snd_algEquiv_twoChartModel_x1_mul
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

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (O : Subring (AlgebraicClosure ℚ)) (hO : O ≤ Pl.toSubring)
    (ρO : A →+* ↥O) (hρO : O.subtype.comp ρO = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ)

    (hπk : Function.Surjective ⇑πk)

    (red₂ : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) →
      AlgebraicCurve.Place k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hred₂ : ∀ (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)))
        (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) (ModularCurve.TwoChart.modelTo A (↥K) j))
        (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂),
      Spec.map (CommRingCat.ofHom O.subtype) ≫ ξ.1 =
        (Mη.pointEquivPlace.symm P).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) →
      c.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
        Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ ξ.1 →
      red₂ P = Mdl₂.pointEquivPlace ⟨c.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact c.2⟩) :
    ∃ S₀ : Finset (AlgebraicCurve.Place k ↥(ModularCurve.igusaFunctionFieldX1C k M w)),
      ∀ (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)))
        (ψ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* ↥O) (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂),

        Spec.map (CommRingCat.ofHom O.subtype) ≫ Spec.map (CommRingCat.ofHom ψ) ≫ ModularCurve.TwoChart.ιFin A (↥K) j =
          (Mη.pointEquivPlace.symm P).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) →

        c.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
          Spec.map (CommRingCat.ofHom ((πk.comp (Subring.inclusion hO)).comp ψ)) ≫ ModularCurve.TwoChart.ιFin A (↥K) j →

        red₂ P ∉ S₀ →
        ((πk.comp (Subring.inclusion hO)).comp ψ) (ModularCurve.TwoChart.jChartFin A (↥K) j) ^ (p ^ 2) ≠ ((πk.comp (Subring.inclusion hO)).comp ψ) (ModularCurve.TwoChart.jChartFin A (↥K) j) := by sorry
