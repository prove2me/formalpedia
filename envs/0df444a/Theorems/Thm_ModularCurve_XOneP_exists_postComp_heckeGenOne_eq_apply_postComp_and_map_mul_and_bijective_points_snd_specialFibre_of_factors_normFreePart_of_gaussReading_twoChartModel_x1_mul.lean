-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_postComp_heckeGenOne_eq_apply_postComp_and_map_mul_and_bijective_points_snd_specialFibre_of_factors_normFreePart_of_gaussReading_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_postComp_heckeGenOne_eq_apply_postComp_and_map_mul_and_bijective_points_snd_specialFibre_of_factors_normFreePart_of_gaussReading_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/2e2bd3cd-15b4-5f6e-8d95-8207df40b70f
-- title:
--   Uₚ on the second Picard factor of the special fibre
-- statement:
--   Fix a prime $p$ and $M$ with $5 \le M$ and $p \nmid M$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, let $\zeta \in L$ be a primitive $p$-th root of unity, and let $K$ be an intermediate field of $L \subseteq \operatorname{LaurentSeries} L$ with $K =$ [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. $K$ is generated over $L$ by the coefficientwise image of the function field of $X_1(Mp)$ over $\mathbb{Q}$ inside Laurent series. Let $A$ be a discrete valuation domain with fraction field $L$, with $p$ in its maximal ideal and with $\zeta$ in the image of $A$, made an $A$-algebra compatibly with $K$, and let $j \in K$ be the element whose Laurent expansion is the coefficientwise image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), assumed nonzero. The curve in play throughout is the two-chart model [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) over $\operatorname{Spec} A$, glued from the spectra of the integral closures of $A[j]$ and of $A[j^{-1}]$ in $K$; it is assumed proper.
--
--   Special-fibre data. Let $k$ be an algebraically closed field of characteristic $p$ and an $A$-algebra, and let $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$ be proper, smooth of relative dimension $1$, geometrically integral, with closed immersions $i_1, i_2$ of $C_1, C_2$ into the base change of the model to $k$, over $\operatorname{Spec} k$. The hypothesis `hcover` says every point of that base change lies in the image of $i_1$ or of $i_2$; `hred` says the scheme-theoretic intersection $C_1 \times_{X_k} C_2$ is reduced, and `hn`, `hn0` give it exactly $n > 0$ points. Sections $\varepsilon$ of the model over $\operatorname{Spec} A$ and $\varepsilon_1, \varepsilon_2$ of $c_1, c_2$ are given, with `hε₁`: $\varepsilon_1$ followed by $i_1$ is the base change of $\varepsilon$ to $k$.
--
--   Relative Picard data. $D$ is a `RelativePic0Designation` for the model over $A$ (a scheme $D.P$ with a structure morphism `D.toBase` to $\operatorname{Spec} A$ and a zero section), `hrep` asserts that $D$ represents the functor of rigidified line bundles on the model which are fibrewise algebraically equivalent to zero (the condition `algEquivZeroCut`), and `hsm`, `hsep` assert that `D.toBase` is smooth and separated. The hypothesis `hreps` provides such a representation for the base change of the model and of $D$ to $k$, and `hPk` an isomorphism of the corresponding Poincaré bundles under base change; $D_1, D_2$ with `hrep₁`, `hrep₂` are representing designations for $c_1, c_2$ with sections $\varepsilon_1, \varepsilon_2$. A morphism $\nu_2$ over $\operatorname{Spec} k$ from $(D.\mathrm{baseChange}\,k).\mathrm{toBase}$ to $D_2.\mathrm{toBase}$ is given, characterised by `hν₂`: for every $k$-scheme $t : T \to \operatorname{Spec} k$ and every point $a$ of $D_k$ over $t$, the pullback of the Poincaré bundle of $D_2$ along $a$ followed by $\nu_2$ is isomorphic to the $\varepsilon_2$-rigidification of the restriction along `curveChange i₂` of the bundle classified by $a$; thus $\nu_2$ is the restriction-to-$C_2$ map on relative Picard functors.
--
--   Characteristic-zero and Galois data. Compatible $A$- and $L$-algebra structures on $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` are fixed; `hsmL`, `hgiL` state that the base change of the model to $L$ is smooth of relative dimension $1$ and geometrically integral, and `hprL`, `hgcL` that the base change of `D.toBase` along $\operatorname{Spec} L \to \operatorname{Spec} A$ is proper and geometrically connected. A curve model $M\eta$ over $\overline{\mathbb{Q}}$ of the function field [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) is given together with an isomorphism $e\eta$ onto the geometric fibre of the two-chart model, compatible with the structure morphisms (`heη`); `Mη_chart_nonempty` says the preimage of the finite chart is nonempty, and `hMηpin` pins the identification: for every element $a$ of the finite chart algebra, the associated element of the function field of $M\eta$ has Laurent expansion the coefficientwise image of the expansion of $a$. The hypothesis `hgal` is the Galois compatibility: for $g \in \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ fixing $L$ pointwise and $\overline{\mathbb{Q}}$-points $x, x'$ of $M\eta.C$ with $x'$ obtained from $x$ by precomposition with $\operatorname{Spec} g$ (after the chart projection), the place attached to $x'$ is the `arithmeticGalois` translate by $g$ of the place attached to $x$. The hypotheses `hin` (`HeckeDiamondInputsAll (M * p)`) and `hcomm` (`HeckeDiamondCommuteBar (M * p)`) supply the inputs making Hecke and diamond operators available and commuting on $J_1(Mp)$, and a semiring action of $\operatorname{Gal}(L/\mathbb{Q})$ on $A$ compatible with the inclusion $A \to L$ is given by `hΓA`.
--
--   Group-theoretic frame of the special fibre. $G$ is a [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9): abelian groups $J_{0s}$, $J_I$, $J_E$, a subgroup `torus` of $J_{0s}$ and a surjective homomorphism $\mathrm{proj} : J_{0s} \to J_I \times J_E$ with kernel the torus. Bijections `pts`, `ptsI`, `ptsE` identify $J_{0s}$, $J_I$, $J_E$ with the $k$-points of $D_k$, $D_1$, $D_2$; `hadd`, `haddI`, `haddE` say that these bijections are additive, in the form that the Poincaré pullback along the sum is isomorphic to the tensor product of the pullbacks; and `hproj` says that under `ptsI`, `ptsE` the two components of $\mathrm{proj}$ become composition with the pullback morphism $D_k \to D_1$ attached to $i_1$ and composition with $\nu_2$ respectively.
--
--   Hecke and Galois structure on $D$. A bijection `gpts` identifies [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186) with the $\overline{\mathbb{Q}}$-points of `D.toBase`; $\varphi$ assigns to each element of the Hecke–diamond algebra `HeckeAlgOne` an endomorphism of `D.toBase` over $\operatorname{Spec} A$, and $\tau$ assigns to each $s \in \operatorname{Gal}(L/\mathbb{Q})$ a semilinear endomorphism of $D.P$ over $\operatorname{Spec}$ of the action of $s$ on $A$. The hypotheses are: `hφmul`, each $\varphi(t)$ is additive for the relative group law carried by $D$; `hφpts`, `gpts` intertwines the Hecke module structure `heckeModuleOneBar` on $J_1(Mp)$ with postcomposition by $\varphi(t)$; `hτ1`, `hτmul`, $\tau$ is multiplicative in the diagrammatic order; `hτφ`, each $\tau(s)$ commutes with each $\varphi(t)$; `hgadd`, `gpts` is additive; and `hτpts`, the Galois action on $J_1(Mp)$ corresponds to precomposition with $\operatorname{Spec} \sigma'$ and postcomposition with $\tau(s^{-1})$ for $\sigma'$ restricting to $s$ on $L$.
--
--   Abel–Jacobi data over $L$ and over $\overline{\mathbb{Q}}$. Given are: `hDL`, a representation statement for the base changes to $L$; a morphism `ajL` from the curve over $L$ to $D_L$ over $\operatorname{Spec} L$; the comparison morphism `kL` between the geometric and the $L$-fibre, with `hkL₁`, `hkL₂` identifying its two components; a morphism `ajbar` from $M\eta.C$ to $D.P$ and a $\overline{\mathbb{Q}}$-point `εbar` of $M\eta.C$; `hPL`, the Poincaré comparison over $L$; `hajLε`, `ajL` sends the cusp section to the zero section; `hajL`, the Abel–Jacobi property of `ajL`: for every field $K'$, every $K'$-point $x$ of the curve over $L$, the pullback of the Poincaré bundle along $x$ followed by `ajL` is the tensor product of the line bundle of the relative effective Cartier divisor of $x$ with the ideal module of the divisor of the section $\varepsilon$, i.e. the class of $x - \varepsilon$; `hajbar`, `hajbar_over`, that `ajbar` is $e\eta$ followed by `kL`, `ajL` and the first projection, and lies over the base; `hεbar`, `hεbar_aj`, that `εbar` is the cusp and is sent to the zero section; and `hpts_aj`, that for all $\overline{\mathbb{Q}}$-points $x, s$ of $M\eta.C$ with $s$ the cusp there is a degree-zero divisor equal to $[\,\text{place of } x\,] - [\,\text{place of } s\,]$ whose class under `gpts` is $x$ followed by `ajbar`.
--
--   Gauss reading on $C_1$. $w$ is an `IntegralWeightOneForm k M`: a weight-one modular form on $\Gamma_1(M)$ together with an integral power series realising its $q$-expansion, whose reduction to $k$ is nonzero. $\mathrm{Mdl}_1$ is a curve model over $k$ of the Igusa function field [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35) (the function field of $X_1(M)$ over $k$ adjoined the inverse of the reduced $q$-expansion of $w$), with an isomorphism $e_1 : \mathrm{Mdl}_1.C \cong C_1$ over $k$ (`he₁`), the chart preimage being nonempty (`hne₁`). The hypothesis `hgauss₁` is the Gauss-reading normalisation: whenever $a$ lies in the finite chart algebra and $x, y$ are power series over $A$ with $y$ having nonzero reduction in $k$ and $a \cdot y = x$ as Laurent series over $L$, the element of the Igusa function field corresponding to $a$ under $e_1$ and $i_1$ has Laurent expansion the quotient of the reductions of $x$ and $y$. Thus $C_1$ is the component on which $q$-expansions reduce coefficientwise, and $C_2$ the other one. The hypothesis `hεC₂` says the reduced cusp section avoids the image of $i_2$, and `hεgal` says $\varepsilon$ is Galois-equivariant: for $s \in \operatorname{Gal}(L/\mathbb{Q})$, any endomorphism $ws$ of the two-chart model lying over $\operatorname{Spec}$ of the action of $s$ on $A$, and any ring automorphism $\rho_s$ of the finite chart algebra inducing coefficientwise application of $s$ on Laurent expansions and compatible with $ws$ on the finite chart, one has $\varepsilon$ followed by $ws$ equal to $\operatorname{Spec}$ of the action of $s$ followed by $\varepsilon$.
--
--   The norm-free abelian subscheme. Given are $\mathcal{A}$ with $a : \mathcal{A} \to \operatorname{Spec} A$ and a morphism $\iota$ from $\mathcal{A}$ to $D.P$ over $a$, and the hypothesis `h𝒜`, a conjunction of: $\iota$ is a closed immersion; $a$ is proper and smooth with connected geometric fibres over every algebraically closed field; for every base $T \to \operatorname{Spec} A$ the image of $\iota$ on $T$-points contains the identity and is closed under the multiplication and the inversion of the relative group law of $D$; the $\overline{\mathbb{Q}}$-points of $D$ factoring through $\iota$ are exactly the images under `gpts` of the subgroup [`ModularCurve.normFreePartAt (M * p) p`](def/ModularCurve_X1PrimitiveSpecializationAtP.html#L29) of $J_1(Mp)$, the image of the endomorphism $x \mapsto |S| x - \sum_{d \in S} \langle d \rangle x$ where $S$ is the set of residues mod $Mp$ coprime to $Mp$ and congruent to $1$ mod $M$; and the image of $\iota$ on $T$-points is stable under every $\varphi(t)$.
--
--   Residue data. $\mathrm{Pl}$ is a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit in it, $\rho : A \to \mathrm{Pl}$ induces the structure map to $\overline{\mathbb{Q}}$ (`hρ`), $O$ is a subring of $\overline{\mathbb{Q}}$ contained in $\mathrm{Pl}$ with a map $\rho_O$ from $A$ inducing the structure map (`hρO`), and $\pi_k : \mathrm{Pl} \to k$ satisfies `hAlgk`, that the structure map $A \to k$ is $\pi_k \circ \rho$, and `hπk`, that $\pi_k$ is surjective.
--
--   Conclusion. Under these hypotheses there exists a self-map $\Phi_2$ of the set of $k$-points of $D_2$ (sections of $D_2.\mathrm{toBase}$ over the identity of $\operatorname{Spec} k$) such that the following three statements hold.
--
--   First, for all $k$-points $v, v'$ of $(D.\mathrm{baseChange}\,k).\mathrm{toBase}$: if there is a morphism $w : \operatorname{Spec} k \to \mathcal{A}$ over $\operatorname{Spec} A$ such that $v$ followed by the first projection of $D.P \times_{\operatorname{Spec} A} \operatorname{Spec} k$ equals $w$ followed by $\iota$, and if $v'$ followed by that projection equals $v$ followed by that projection and then by $\varphi(\mathrm{heckeGenOne}\,p)$, the Hecke endomorphism attached to the generator at the prime $p$, then $\Phi_2$ applied to $\nu_2 \circ v$ equals $\nu_2 \circ v'$ (in Lean, $\mathrm{postComp}\,\nu_2\,v' = \Phi_2(\mathrm{postComp}\,\nu_2\,v)$).
--
--   Second, $\Phi_2$ is a homomorphism for the group law on $k$-points of $D_2$ coming from `hrep₂`: for all $k$-points $x, y$ of $D_2$, $\Phi_2$ of the product of $x$ and $y$ is the product of $\Phi_2 x$ and $\Phi_2 y$.
--
--   Third, $\Phi_2$ is bijective.
--
--   The first clause constrains $\Phi_2$ only on the $\nu_2$-images of those $k$-points of $D_k$ which factor through $\mathcal{A}$, while the second and third clauses hold for all $k$-points of $D_2$.
--
--   This is the Eichler–Shimura-type statement at the prime $p$ in the scheme-level frame for $X_1(Mp)$ over a discrete valuation ring with residue characteristic $p$: on the component of the special fibre which is not the one carrying the coefficientwise reduction of $q$-expansions, the Hecke operator at $p$ induces, at the level of $k$-points of the relative $\mathrm{Pic}^0$ factor $D_2$, a single bijective group homomorphism $\Phi_2$. It is used by [`ModularCurve.XOneP.normFreePartFamily_exists_addEquiv_toPic0Pair_sp_heckeOperatorOneBar_snd_eq_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.normFreePartFamily_exists_addEquiv_toPic0Pair_sp_heckeOperatorOneBar_snd_eq_twoChartModel_x1_mul), which transports this description of the action at $p$ to the norm-free part of the Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_postComp_heckeGenOne_eq_apply_postComp_and_map_mul_and_bijective_points_snd_specialFibre_of_factors_normFreePart_of_gaussReading_twoChartModel_x1_mul.lean

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
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.exists_postComp_heckeGenOne_eq_apply_postComp_and_map_mul_and_bijective_points_snd_specialFibre_of_factors_normFreePart_of_gaussReading_twoChartModel_x1_mul
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

    (hsmL : SmoothOfRelativeDimension 1 (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))
    (hgiL : GeometricallyIntegral (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))

    (hprL : IsProper (pullback.snd D.toBase (specMap A L)))
    (hgcL : GeometricallyConnected (pullback.snd D.toBase (specMap A L)))

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
    (hin : ModularCurve.HeckeDiamondInputsAll (M * p)) (hcomm : ModularCurve.HeckeDiamondCommuteBar (M * p))

    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a))

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
    (φ : ModularCurve.HeckeAlgOne → SchemeHomOver D.toBase D.toBase)
    (τ : ∀ s : L ≃ₐ[ℚ] L,
      SchemeHomOver (D.toBase ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s))) D.toBase)
    (hφmul : ∀ (t : ModularCurve.HeckeAlgOne) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s x y) (φ t) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
          (NeronModelInfra.schemeHomOverComp x (φ t)) (NeronModelInfra.schemeHomOverComp y (φ t)))
    (hφpts : letI := ModularCurve.heckeModuleOneBar (M * p)
      ∀ (t : ModularCurve.HeckeAlgOne) (x : ModularCurve.JOne (M * p)), (gpts (t • x)).1 = (gpts x).1 ≫ (φ t).1)
    (hτ1 : (τ 1).1 = 𝟙 D.P) (hτmul : ∀ s s' : L ≃ₐ[ℚ] L, (τ (s * s')).1 = (τ s).1 ≫ (τ s').1)
    (hτφ : ∀ (t : ModularCurve.HeckeAlgOne) (s : L ≃ₐ[ℚ] L), (τ s).1 ≫ (φ t).1 = (φ t).1 ≫ (τ s).1)

    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))
    (hτpts : ∀ (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (s : L ≃ₐ[ℚ] L),
      (∀ l : L, σ' (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) (s l)) →
      ∀ x : ModularCurve.JOne (M * p),
        (gpts (σ' • x)).1 = Spec.map (CommRingCat.ofHom σ'.toRingEquiv.toRingHom) ≫ (gpts x).1 ≫ (τ s⁻¹).1)

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

    (hεC₂ : ∀ t, ((sectionBaseChange k ε).1).base t ∉ Set.range i₂.1.base)
    (hεgal : ∀ (s : L ≃ₐ[ℚ] L) (ws : ModularCurve.TwoChartModel A (↥K) j ⟶ ModularCurve.TwoChartModel A (↥K) j),
      ws ≫ ModularCurve.TwoChart.modelTo A (↥K) j =
        ModularCurve.TwoChart.modelTo A (↥K) j ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)) →
      ∀ (ρs : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ≃+* ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)),
      (∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
        (((ρs b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L) =
          ModularCurve.coeffMap (s.toAlgHom.toRingHom) (((b : ↥K)) : LaurentSeries L)) →
      ModularCurve.TwoChart.ιFin A (↥K) j ≫ ws = Spec.map (CommRingCat.ofHom ρs.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j →
      ε.1 ≫ ws = Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)) ≫ ε.1)

    (𝒜 : Scheme.{0}) (a : 𝒜 ⟶ Spec (CommRingCat.of A)) (ι : SchemeHomOver a D.toBase)
    (h𝒜 :

      IsClosedImmersion ι.1 ∧

      IsProper a ∧ Smooth a ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)),
        ConnectedSpace ↥(pullback a s)) ∧

      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)),
        (∃ o : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp o ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).one s) ∧
        (∀ x y : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
            (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι)) ∧
        (∀ x : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).inv s
            (NeronModelInfra.schemeHomOverComp x ι))) ∧

      (∀ x : ModularCurve.JOne (M * p),
        x ∈ ModularCurve.normFreePartAt (M * p) p ↔
          ∃ y : SchemeHomOver (specMap A (AlgebraicClosure ℚ)) a, y.1 ≫ ι.1 = (gpts x).1) ∧

      (∀ (t : ModularCurve.HeckeAlgOne) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x : SchemeHomOver s a),
        ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp x ι) (φ t)))

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (O : Subring (AlgebraicClosure ℚ)) (hO : O ≤ Pl.toSubring)
    (ρO : A →+* ↥O) (hρO : O.subtype.comp ρO = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ)

    (hπk : Function.Surjective ⇑πk) :
    ∃ Φ₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₂.toBase → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₂.toBase,

      (∀ (v v' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase),
      (∃ w : Spec (CommRingCat.of k) ⟶ 𝒜, w ≫ a = specMap A k ∧
          v.1 ≫ pullback.fst D.toBase (specMap A k) = w ≫ ι.1) →
      v'.1 ≫ pullback.fst D.toBase (specMap A k) = (v.1 ≫ pullback.fst D.toBase (specMap A k)) ≫ (φ (ModularCurve.heckeGenOne ⟨p, Fact.out⟩)).1 →
        postComp ν₂ v' = Φ₂ (postComp ν₂ v)) ∧

      (∀ x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₂.toBase,
        Φ₂ ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₂.some).mul (𝟙 (Spec (CommRingCat.of k))) x y) =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₂.some).mul (𝟙 (Spec (CommRingCat.of k))) (Φ₂ x) (Φ₂ y)) ∧

      Function.Bijective Φ₂ := by sorry
