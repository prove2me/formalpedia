-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_coprime_algEquiv_finset_red_smul_diamondAutBar_smul_eq_and_red_smul_eq_smul_frob_smul_of_gaussReduces_smul_twoChartModel_x1_mul_of_atkinLehner_of_diamondConj
-- name    : ModularCurve.XOneP.exists_coprime_algEquiv_finset_red_smul_diamondAutBar_smul_eq_and_red_smul_eq_smul_frob_smul_of_gaussReduces_smul_twoChartModel_x1_mul_of_atkinLehner_of_diamondConj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/b14bc841-9f19-5103-8def-594b0d614a73
-- title:
--   Eichler–Shimura relation read through σ on the Igusa curve
-- statement:
--   **Arithmetic data.** Fix a prime $p$ and a nonzero natural number $M$ with $5 \le M$ and $p \nmid M$ (`hM`, `hpM`). Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, and let $\zeta \in L$ be a primitive $p$-th root of unity (`hζ`). Let $K$ be an intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ which, by `hK`, equals [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), that is, the subfield of $L((q))$ generated over $L$ by the coefficientwise image under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of the $q$-expansion function field of $X_1(Mp)$ over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with fraction field $L$, acting on $K$ compatibly with $L$ (scalar tower), with $p$ in the maximal ideal of $A$ (`hAp`) and $\zeta$ in the image of $A \to L$ (`hζA`). Let $j \in K$ be a nonzero element whose Laurent expansion is the coefficientwise image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) (`hj`). The associated two-chart integral model [`ModularCurve.TwoChart.modelTo A ↥K j`](def/ModularCurve_TwoChartModel.html#L252) is the structure morphism to $\operatorname{Spec} A$ of the pushout glueing the spectra of the subalgebras of elements of $K$ integral over $A[j]$ and over $A[j^{-1}]$; it is assumed proper.
--
--   **Geometry in characteristic $p$.** Let $k$ be an algebraically closed field of characteristic $p$ which is an $A$-algebra. Let $C_1, C_2$ be schemes with morphisms $c_1, c_2$ to $\operatorname{Spec} k$, each proper, smooth of relative dimension $1$ and geometrically integral, and let $i_1, i_2$ be closed immersions of $C_1, C_2$ into the base change of the two-chart model along $A \to k$, compatible with the structure morphisms. The hypothesis `hcover` says that every point of the pullback of [`ModularCurve.TwoChart.modelTo A ↥K j`](def/ModularCurve_TwoChartModel.html#L252) along `specMap A k` lies in the image of $i_1$ or of $i_2$; `hred` says that the scheme-theoretic intersection `pullback i₁.1 i₂.1` is reduced; $n$ is its number of points (`hn`) and $0 < n$ (`hn0`).
--
--   **The curve over $\overline{\mathbb{Q}}$.** The algebraic closure $\overline{\mathbb{Q}}$ is an $A$- and an $L$-algebra with the evident scalar tower. Let $M\eta$ be a `CurveModel` over $\overline{\mathbb{Q}}$ for [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) (the $\overline{\mathbb{Q}}$-base change of the function field of $X_1(Mp)$): a proper smooth integral curve together with an isomorphism of that field with its function field and a bijection from its closed points to the places. Let $e\eta$ be an isomorphism from $M\eta.C$ to the $\overline{\mathbb{Q}}$-fibre of the two-chart model compatible with the structure morphisms (`heη`). The hypothesis `hMηpin` pins the identification: for every $a$ in the finite chart algebra [`ModularCurve.TwoChart.chartAlgFin A ↥K j`](def/ModularCurve_TwoChartModel.html#L135), the element of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) obtained by pulling $a$ back along $e\eta$ followed by the first projection, taking the germ at the generic point and transporting through $M\eta.\mathrm{ffEquiv}^{-1}$, has Laurent expansion the coefficientwise image under $L \to \overline{\mathbb{Q}}$ of the Laurent expansion of $a$. The hypothesis `hgal` is the Galois equivariance of the point–place dictionary: for every $g \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ fixing the image of $L$ pointwise and for all $\overline{\mathbb{Q}}$-points $x, x'$ of $M\eta.C$ (sections of $M\eta.\mathrm{toBase}$), if $x'$ followed by $e\eta$ and the first projection equals $\operatorname{Spec}(g)$ followed by $x$, $e\eta$ and the first projection, then $M\eta.\mathrm{pointEquivPlace}\,x' = \mathrm{arithmeticGalois}\,(x_1\text{-field of } Mp)(g) \cdot M\eta.\mathrm{pointEquivPlace}\,x$, the action being that of the semilinear automorphism attached to $g$ on places.
--
--   **The Igusa side.** Let $w$ be a [`ModularCurve.IntegralWeightOneForm k M`](def/ModularCurve_IgusaFunctionFieldX1.html#L16): a weight-one modular form on $\Gamma_1(M)$ together with an integral power series realising its $q$-expansion, whose reduction to $k$ is nonzero. Let $\mathrm{Ig} =$ [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35), the Igusa function field over the $q$-expansion function field of $X_1(M)$ over $k$ attached to the Hasse-root function of $w$. Let $\mathrm{Mdl}_1$ be a `CurveModel` over $k$ for $\mathrm{Ig}$, with an isomorphism $e_1$ onto $C_1$ compatible with the structure morphisms (`he₁`). The hypothesis `hgauss₁` is the Gauss-reduction reading of the chart: for every $a$ in the finite chart algebra and all power series $x, y$ over $A$ with $\bar y \ne 0$ in $k[[q]]$, if $a \cdot y = x$ holds in $L((q))$ after applying $A \to L$, then the element of $\mathrm{Ig}$ obtained by pulling $a$ back along $e_1$ followed by $i_1$ and the first projection, taking the germ at the generic point and transporting through $\mathrm{Mdl}_1.\mathrm{ffEquiv}^{-1}$, has Laurent expansion $\bar x / \bar y$ over $k$.
--
--   **The automorphism $\sigma$ and its companions.** Let $\sigma$ be an $L$-algebra automorphism of $K$ subject to: `hσj`, that $\sigma j$ has Laurent expansion the image of [`ModularCurve.qExpand ℚ p ModularCurve.jq`](def/ModularCurve_X0.html#L25) (the $j$-expansion in $q^p$); `hσfin`, that $b$ lies in the finite chart algebra if and only if $\sigma b$ does; `hσW`, which requires of every valuation subring $W_0$ of $K$ characterised by the Gauss condition ($f \in W_0$ if and only if there are power series $x, y$ over $A$ with nonzero residual $y$ and $f \cdot y = x$ in $L((q))$) both that the preimage of $W_0$ under $\sigma$ differs from $W_0$, and that for every polynomial $P$ over $A$ with nonzero reduction both $P(j)$ and $P(j)^{-1}$ lie in that preimage; `hσAL`, that on elements of the full modular function field of level $Mp$ that lie in $K$ after coefficient embedding, $\sigma$ acts as [`ModularCurve.atkinLehnerInvolutionFull M p`](def/ModularCurve_AtkinLehnerPartial.html#L21); and `hdiamConj`, the diamond conjugation rule: for all $d, d'$ coprime to $Mp$ with $d' \equiv d \bmod M$ and $d'd \equiv 1 \bmod p$, and for any $L$-automorphisms $\theta_d, \theta_{d'}$ of $K$ that realise the base-changed diamond automorphisms `baseChangeAut L (diamondAut (M*p) d)` and `baseChangeAut L (diamondAut (M*p) d')` in the sense of agreement of Laurent expansions, one has $\sigma \theta_d \sigma^{-1} = \theta_{d'}$ on $K$ (as Laurent expansions). Let $\bar\sigma$ be a $\overline{\mathbb{Q}}$-algebra automorphism of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) compatible with $\sigma$ under the coefficient map $L \to \overline{\mathbb{Q}}$ (`hσbar`).
--
--   **Frobenius and Hecke data.** Let $\mathrm{frob}_{\mathrm{Ig}}$ be a semilinear automorphism of $\mathrm{Ig}$ over $k$ (a pair of ring automorphisms of $\mathrm{Ig}$ and of $k$ compatible with the structure map) which raises every Laurent coefficient to the $p$-th power (`hfrobIg`). Assume `hβdef`, that $q \mapsto q^p$ carries the function field of $X_1(Mp)$ into that of $X_1(Mp) \cap X_0(Mp\cdot p)$; assume the integrality hypotheses `hα` and `hβ` for the two maps `heckeAlphaOneBar` and `heckeBetaOneBar` over $\overline{\mathbb{Q}}$; assume principal divisors exist for the $\overline{\mathbb{Q}}$-base change of the $X_1 \cap X_0$ function field; and assume `hdeg`, that the degree of $\overline{\mathbb{Q}}(X_1(Mp) \cap X_0(Mp \cdot p))$ over $\overline{\mathbb{Q}}(X_1(Mp))$ along `heckeBetaOneBar` equals $p$.
--
--   **Conclusion.** There exist a natural number $d$ coprime to $Mp$, a $k$-algebra automorphism $\delta$ of $\mathrm{Ig}$, and a finite set $S_1$ of places of $\mathrm{Ig}$ over $k$, such that the following holds for every choice of reduction data, namely: a valuation subring $Pl$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $Pl$; a ring homomorphism $\rho : A \to Pl$ lifting $A \to \overline{\mathbb{Q}}$; a subring $O$ of $\overline{\mathbb{Q}}$ with $O \le Pl$ and a lift $\rho_O : A \to O$ of $A \to \overline{\mathbb{Q}}$; a surjective ring homomorphism $\pi_k : Pl \to k$ with $A \to k$ equal to $\pi_k \circ \rho$; the reverse inclusion $Pl \le O$; and a map $\mathrm{red}_1$ from places of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) over $\overline{\mathbb{Q}}$ to places of $\mathrm{Ig}$ over $k$ satisfying `hred₁`: whenever a place $P$, an $O$-point $\xi$ of the two-chart model over $\operatorname{Spec}\rho_O$ and a $k$-point $c$ of $C_1$ satisfy that $\operatorname{Spec}$ of the inclusion $O \hookrightarrow \overline{\mathbb{Q}}$ followed by $\xi$ equals the $\overline{\mathbb{Q}}$-point $M\eta.\mathrm{pointEquivPlace}^{-1}(P)$ followed by $e\eta$ and the first projection, and that $c$ followed by $i_1$ and the first projection equals $\operatorname{Spec}(\pi_k \circ (O \hookrightarrow Pl))$ followed by $\xi$, then $\mathrm{red}_1 P$ is the place of $\mathrm{Ig}$ attached by $\mathrm{Mdl}_1.\mathrm{pointEquivPlace}$ to the $k$-point $c$ followed by $e_1^{-1}$.
--
--   Say that a place $R$ *reduces through the finite chart* if there are an $O$-point $\xi$ of the two-chart model over $\operatorname{Spec}\rho_O$ and a $k$-point $c$ of $C_1$ such that (i) $\operatorname{Spec}(O \hookrightarrow \overline{\mathbb{Q}})$ followed by $\xi$ equals $M\eta.\mathrm{pointEquivPlace}^{-1}(R)$ followed by $e\eta$ and the first projection; (ii) $c$ followed by $i_1$ and the first projection equals $\operatorname{Spec}(\pi_k \circ (O \hookrightarrow Pl))$ followed by $\xi$; (iii) no point of the image of $c$ lies in the image of the first projection of `pullback i₁.1 i₂.1`; and (iv) every point of the image of $c$ followed by $i_1$ and the first projection lies in the image of [`ModularCurve.TwoChart.ιFin A ↥K j`](def/ModularCurve_TwoChartModel.html#L231), the morphism from the spectrum of the finite chart algebra into the two-chart model.
--
--   The two asserted conjuncts are then:
--
--   (1) For all places $P, P_1, P_2, P_{21}$ of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) with $P_1 = \bar\sigma \cdot P$, $P_2 = \langle d \rangle \cdot P$ for the diamond automorphism [`ModularCurve.diamondAutBar (M * p) d`](def/ModularCurve_X1Diamond.html#L94), and $P_{21} = \bar\sigma \cdot P_2$ (actions through `SemilinearAut.ofAlgAut`): if $P_1$ reduces through the finite chart, then $P_{21}$ reduces through the finite chart and $\mathrm{red}_1 P_{21} = \delta \cdot \mathrm{red}_1 P_1$, the action of $\delta$ on places being through `SemilinearAut.ofAlgAut`.
--
--   (2) For all places $P, P_1, P_2, P_{21}, Q_p, Q_{p1}$ with $P_1 = \bar\sigma \cdot P$, $P_2 = \langle d \rangle \cdot P$, $P_{21} = \bar\sigma \cdot P_2$ and $Q_{p1} = \bar\sigma \cdot Q_p$: if $P_1$ reduces through the finite chart, $Q_{p1}$ reduces through the finite chart, $\mathrm{red}_1 P_1 \notin S_1$, and $Q_p$ lies in the support of [`ModularCurve.heckeDivOneBar hα hβ`](def/ModularCurve_X1HeckeOperator.html#L151) applied to the divisor $1 \cdot P$ (the divisor correspondence obtained by pulling back along `heckeBetaOneBar` and pushing forward along `heckeAlphaOneBar`), then $\mathrm{red}_1 Q_{p1} = \mathrm{frob}_{\mathrm{Ig}} \cdot \mathrm{red}_1 P_{21}$.
--
--   This is the place-level Eichler–Shimura congruence for $X_1(Mp)$ in characteristic $p$, transported through the Atkin–Lehner-type automorphism $\sigma$ so that both branches of the $U_p$-correspondence are read on the Gauss side, with the supersingular-type exceptions absorbed into a finite set $S_1$ of places of the Igusa function field and the accompanying diamond twist pinned as a single automorphism $\delta$. The quantification of the place data ($Pl$, $O$, $\pi_k$, $\mathrm{red}_1$) inside the existential for $d$, $\delta$, $S_1$ makes those three uniform in the chosen place of $\overline{\mathbb{Q}}$ above $p$; the result feeds [`ModularCurve.XOneP.exists_coprime_algEquiv_finset_red_diamondAutBar_smul_eq_smul_and_red_eq_smul_frob_smul_red_of_reducesSnd_of_gaussReading_snd_algEquiv_twoChartModel_x1_mul_of_atkinLehner_of_diamondConj`](thm.html#ModularCurve.XOneP.exists_coprime_algEquiv_finset_red_diamondAutBar_smul_eq_smul_and_red_eq_smul_frob_smul_red_of_reducesSnd_of_gaussReading_snd_algEquiv_twoChartModel_x1_mul_of_atkinLehner_of_diamondConj), on the route to level lowering at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_coprime_algEquiv_finset_red_smul_diamondAutBar_smul_eq_and_red_smul_eq_smul_frob_smul_of_gaussReduces_smul_twoChartModel_x1_mul_of_atkinLehner_of_diamondConj.lean

import Mathlib
import Definitions.Def_ModularCurve_AtkinLehnerPartial
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
import Definitions.Def_ModularCurve_X1Diamond
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

theorem ModularCurve.XOneP.exists_coprime_algEquiv_finset_red_smul_diamondAutBar_smul_eq_and_red_smul_eq_smul_frob_smul_of_gaussReduces_smul_twoChartModel_x1_mul_of_atkinLehner_of_diamondConj
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

    (hσAL : ∀ (f : ↥(ModularCurve.modularFunctionFieldFull (M * p)))
        (hfK : ModularCurve.coeffEmb L (f : LaurentSeries ℚ) ∈ K),
        ((σ ⟨ModularCurve.coeffEmb L (f : LaurentSeries ℚ), hfK⟩ : ↥K) : LaurentSeries L) =
          ModularCurve.coeffEmb L ((ModularCurve.atkinLehnerInvolutionFull M p f :
            ↥(ModularCurve.modularFunctionFieldFull (M * p))) : LaurentSeries ℚ))

    (hdiamConj : ∀ (d d' : ℕ), d.Coprime (M * p) → d'.Coprime (M * p) →
      ((d' : ZMod M) = (d : ZMod M)) → ((d' : ZMod p) * (d : ZMod p) = 1) →
      ∀ (θd θd' : ↥K ≃ₐ[L] ↥K),
        (∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
        (x : LaurentSeries L) = (x' : LaurentSeries L) →
          ((θd x : ↥K) : LaurentSeries L) =
            ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d) x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L)) →
        (∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
        (x : LaurentSeries L) = (x' : LaurentSeries L) →
          ((θd' x : ↥K) : LaurentSeries L) =
            ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d') x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L)) →
        ∀ x : ↥K, ((σ (θd (σ.symm x)) : ↥K) : LaurentSeries L) = ((θd' x : ↥K) : LaurentSeries L))

    (σbar : ↥(ModularCurve.x1FunctionFieldBar (M * p)) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar (M * p)))
    (hσbar : ∀ (f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) (b : ↥K),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥K) : LaurentSeries L) →
      ((σbar f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((σ b : ↥K) : LaurentSeries L))

    (frobIg : SemilinearAut k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hfrobIg : ∀ (x : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (n : ℤ),
      ((frobIg • x : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k).coeff n = ((x : LaurentSeries k).coeff n) ^ p)

    (hβdef : ModularCurve.HeckeBetaOneDefined (M * p) p)
    (hα : ModularCurve.HeckeAlphaOneBarIntegral (AlgebraicClosure ℚ) (M * p) p)
    (hβ : ModularCurve.HeckeBetaOneBarIntegral (AlgebraicClosure ℚ) (M * p) p)
    [HasPrincipalDivisors (AlgebraicClosure ℚ)
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))]

    (hdeg : AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ) (ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) (M * p) p) = p) :
    ∃ d : ℕ, d.Coprime (M * p) ∧
    ∃ δ : ↥(ModularCurve.igusaFunctionFieldX1C k M w) ≃ₐ[k] ↥(ModularCurve.igusaFunctionFieldX1C k M w),
    ∃ S₁ : Finset (AlgebraicCurve.Place k ↥(ModularCurve.igusaFunctionFieldX1C k M w)),

      ∀ (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
        (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
        (O : Subring (AlgebraicClosure ℚ)) (hO : O ≤ Pl.toSubring)
        (ρO : A →+* ↥O) (hρO : O.subtype.comp ρO = algebraMap A (AlgebraicClosure ℚ))
        (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ)
        (hπk : Function.Surjective ⇑πk)
        (hOPl : Pl.toSubring ≤ O)
        (red₁ : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) →
          AlgebraicCurve.Place k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
        (hred₁ : ∀ (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)))
            (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) (ModularCurve.TwoChart.modelTo A (↥K) j))
            (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
          Spec.map (CommRingCat.ofHom O.subtype) ≫ ξ.1 =
            (Mη.pointEquivPlace.symm P).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) →
          c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
            Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ ξ.1 →
          red₁ P = Mdl₁.pointEquivPlace ⟨c.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact c.2⟩),

      (∀ (P P₁ P₂ P₂₁ : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p))),
        P₁ = SemilinearAut.ofAlgAut σbar • P → P₂ = SemilinearAut.ofAlgAut (ModularCurve.diamondAutBar (M * p) d) • P → P₂₁ = SemilinearAut.ofAlgAut σbar • P₂ →
        (∃ (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) (ModularCurve.TwoChart.modelTo A (↥K) j))
           (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
          Spec.map (CommRingCat.ofHom O.subtype) ≫ ξ.1 =
            (Mη.pointEquivPlace.symm P₁).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ∧
          c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
            Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ ξ.1 ∧
          (∀ t, c.1.base t ∉ Set.range (pullback.fst i₁.1 i₂.1).base) ∧
          ∀ t, (c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base t ∈
            Set.range (ModularCurve.TwoChart.ιFin A (↥K) j).base) →
        (∃ (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) (ModularCurve.TwoChart.modelTo A (↥K) j))
           (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
          Spec.map (CommRingCat.ofHom O.subtype) ≫ ξ.1 =
            (Mη.pointEquivPlace.symm P₂₁).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ∧
          c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
            Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ ξ.1 ∧
          (∀ t, c.1.base t ∉ Set.range (pullback.fst i₁.1 i₂.1).base) ∧
          ∀ t, (c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base t ∈
            Set.range (ModularCurve.TwoChart.ιFin A (↥K) j).base) ∧
        red₁ P₂₁ = SemilinearAut.ofAlgAut δ • red₁ P₁) ∧

      (∀ (P P₁ P₂ P₂₁ Qp Qp₁ : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p))),
        P₁ = SemilinearAut.ofAlgAut σbar • P → P₂ = SemilinearAut.ofAlgAut (ModularCurve.diamondAutBar (M * p) d) • P → P₂₁ = SemilinearAut.ofAlgAut σbar • P₂ → Qp₁ = SemilinearAut.ofAlgAut σbar • Qp →
        (∃ (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) (ModularCurve.TwoChart.modelTo A (↥K) j))
           (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
          Spec.map (CommRingCat.ofHom O.subtype) ≫ ξ.1 =
            (Mη.pointEquivPlace.symm P₁).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ∧
          c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
            Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ ξ.1 ∧
          (∀ t, c.1.base t ∉ Set.range (pullback.fst i₁.1 i₂.1).base) ∧
          ∀ t, (c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base t ∈
            Set.range (ModularCurve.TwoChart.ιFin A (↥K) j).base) →
        (∃ (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) (ModularCurve.TwoChart.modelTo A (↥K) j))
           (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
          Spec.map (CommRingCat.ofHom O.subtype) ≫ ξ.1 =
            (Mη.pointEquivPlace.symm Qp₁).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ∧
          c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
            Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ ξ.1 ∧
          (∀ t, c.1.base t ∉ Set.range (pullback.fst i₁.1 i₂.1).base) ∧
          ∀ t, (c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base t ∈
            Set.range (ModularCurve.TwoChart.ιFin A (↥K) j).base) →
        red₁ P₁ ∉ S₁ →
        Qp ∈ (ModularCurve.heckeDivOneBar (L := AlgebraicClosure ℚ) (M := M * p) (ℓ := p) hα hβ (Finsupp.single P 1)).support →
        red₁ Qp₁ = frobIg • red₁ P₂₁) := by sorry
