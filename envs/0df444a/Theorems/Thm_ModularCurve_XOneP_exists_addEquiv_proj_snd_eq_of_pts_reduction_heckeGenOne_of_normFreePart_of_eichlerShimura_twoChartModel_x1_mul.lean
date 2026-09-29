-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_addEquiv_proj_snd_eq_of_pts_reduction_heckeGenOne_of_normFreePart_of_eichlerShimura_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_addEquiv_proj_snd_eq_of_pts_reduction_heckeGenOne_of_normFreePart_of_eichlerShimura_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/8311a878-100d-5a1d-83da-59debe0f0160
-- title:
--   Uₚ on the étale component J_E of the special fibre
-- statement:
--   **Arithmetic data.** A prime $p$ and a natural number $M \ne 0$ with $5 \le M$ (`hM`) and $p \nmid M$ (`hpM`). A field $L$ of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, together with a primitive $p$-th root of unity $\zeta \in L$. An intermediate field $K$ of $L((q))/L$ which by `hK` is [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield of $L((q))$ generated over $L$ by the coefficientwise image of the function field of $X_1(Mp)$ as realised inside $\mathbb{Q}((q))$. A discrete valuation domain $A$ with fraction field $L$, such that $p$ lies in the maximal ideal of $A$ (`hAp`) and $\zeta$ lies in the image of $A \to L$ (`hζA`), together with an $A$-algebra structure on $K$ compatible with $A \to L \to K$. An element $j \in K$ whose Laurent series is the image under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular invariant (`hj`), assumed nonzero. The associated morphism [`ModularCurve.TwoChart.modelTo A ↥K j`](def/ModularCurve_TwoChartModel.html#L252), glued from the two chart algebras `chartAlgFin` and `chartAlgInf` attached to $j$, is written $X \to \operatorname{Spec} A$ below; it is assumed proper.
--
--   **Geometry of the special fibre.** An algebraically closed field $k$ of characteristic $p$ which is an $A$-algebra; the base change $X_k \to \operatorname{Spec} k$ is `baseChange A (ModularCurve.TwoChart.modelTo A ↥K j) k`. Two schemes $C_1, C_2$ with structure morphisms $c_1, c_2$ to $\operatorname{Spec} k$, each proper, smooth of relative dimension $1$ and geometrically integral, and closed immersions $i_1 : C_1 \to X_k$, $i_2 : C_2 \to X_k$ over $\operatorname{Spec} k$ such that every point of $X_k$ lies in the image of $i_1$ or of $i_2$ (`hcover`); the scheme-theoretic intersection `pullback i₁.1 i₂.1` is reduced (`hred`) and its point set has cardinality $n$ (`hn`) with $n > 0$ (`hn0`). A section $\varepsilon$ of $X \to \operatorname{Spec} A$, sections $\varepsilon_1, \varepsilon_2$ of $c_1, c_2$, and the compatibility `hε₁`: $\varepsilon_1$ followed by $i_1$ is the base change to $k$ of $\varepsilon$.
--
--   **Relative $\mathrm{Pic}^0$ data.** A `RelativePic0Designation` $D$ for $X \to \operatorname{Spec} A$ (a scheme $D.P$ over $\operatorname{Spec} A$ with a zero section) together with `hrep`: $D$ represents the relative Picard functor of $X$ rigidified along $\varepsilon$ and cut out by the condition `algEquivZeroCut`, that is, by fibrewise algebraic triviality; this provides a Poincaré rigidified line bundle satisfying the condition, the universal property that every rigidified line bundle on $X \times_A T$ satisfying it is the pullback of the Poincaré bundle along a unique $T$-point of $D$, and triviality of its pullback along the zero section. Further: $D.\mathrm{toBase}$ is smooth (`hsm`) and separated (`hsep`); `hreps` asserts the corresponding representability statement for $X_k$ with the section $\varepsilon_k$ and the base change $D_k = D \times_A k$; `hPk` asserts that the Poincaré bundle of `hreps` is isomorphic to the base change to $k$ of the pullback of the Poincaré bundle of `hrep` along the first projection $D_k \to D$. Designations $D_1$ for $c_1$ and $D_2$ for $c_2$ with the analogous representability hypotheses `hrep₁`, `hrep₂`. A morphism $\nu_2 : D_k \to D_2$ over $\operatorname{Spec} k$ such that (`hν₂`) for every $k$-scheme $t : T \to \operatorname{Spec} k$ and every $T$-point $a$ of $D_k$, the pullback of the Poincaré bundle of $D_2$ along $a$ followed by $\nu_2$ is isomorphic to the `rigidify`-normalisation, with respect to $\varepsilon_2$, of the pullback along `curveChange i₂` of the pullback of the Poincaré bundle of $D_k$ along $a$; thus $\nu_2$ realises restriction of line bundles along the closed immersion $i_2$.
--
--   **Geometric generic fibre and its function field.** Compatible $A$- and $L$-algebra structures on $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. Hypotheses `hsmL`, `hgiL`: the base change of $X$ to $L$ is smooth of relative dimension $1$ and geometrically integral. Hypotheses `hprL`, `hgcL`: $D_L \to \operatorname{Spec} L$ is proper and geometrically connected. A `CurveModel` $M_\eta$ for the field [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) over $\overline{\mathbb{Q}}$, an isomorphism $e_\eta$ from $M_\eta.C$ to $X \times_A \overline{\mathbb{Q}}$ compatible with the structure morphisms (`heη`), nonemptiness of the preimage of the finite chart (`Mη_chart_nonempty`), and `hMηpin`: for every element $a$ of `chartAlgFin A ↥K j`, the function-field element of $M_\eta$ obtained from $a$ by taking its germ on that preimage corresponds, under $M_\eta.\mathrm{ffEquiv}^{-1}$, to the Laurent series obtained from $a \in K$ by applying [`ModularCurve.coeffMap`](def/ModularCurve_LaurentCoeff.html#L16) to the embedding $L \to \overline{\mathbb{Q}}$. Hypothesis `hgal`: for every $\mathbb{Q}$-automorphism $g$ of $\overline{\mathbb{Q}}$ fixing the image of $L$ pointwise, and all $\overline{\mathbb{Q}}$-points $x, x'$ of $M_\eta.C$, if $x'$ composed with $e_\eta$ followed by the first projection equals $\operatorname{Spec}(g)$ followed by the same composite for $x$, then $M_\eta.\mathrm{pointEquivPlace}\,x' = \mathrm{arithmeticGalois}(\mathrm{x1FunctionField}(Mp))(g) \cdot M_\eta.\mathrm{pointEquivPlace}\,x$. Hypotheses `hin` (`HeckeDiamondInputsAll (M * p)`) and `hcomm` (`HeckeDiamondCommuteBar (M * p)`), which make the Hecke and diamond operators on degree-zero divisor classes available and commuting. A multiplicative semiring action of $\operatorname{Gal}(L/\mathbb{Q})$ on $A$ compatible with its action on $L$ (`hΓA`).
--
--   **Group-theoretic dictionaries on the special fibre.** A term $G$ of [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9): abelian groups $J_s^0$, $J_I$, $J_E$, a subgroup `torus` of $J_s^0$, and a surjective homomorphism $\mathrm{proj} : J_s^0 \to J_I \times J_E$ with kernel `torus`. Bijections `pts` from $J_s^0$ to the $k$-points of $D_k$, `ptsI` from $J_I$ to the $k$-points of $D_1$, `ptsE` from $J_E$ to the $k$-points of $D_2$. Hypotheses `hadd`, `haddI`, `haddE`: each of these bijections is additive in the sense that the Poincaré pullback along the image of a sum is isomorphic to the tensor product of the Poincaré pullbacks along the images of the summands. Hypothesis `hproj`: for every $x \in J_s^0$, $\mathrm{ptsI}((\mathrm{proj}\,x)_1)$ is $\mathrm{pts}(x)$ followed by the comparison morphism `RepresentsRelSubPic.pullbackHom` attached to $i_1$ and `hε₁`, and $\mathrm{ptsE}((\mathrm{proj}\,x)_2)$ is $\mathrm{pts}(x)$ followed by $\nu_2$.
--
--   **Hecke and Galois structure on $D$.** A bijection `gpts` from [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186), the group of degree-zero divisor classes of $X_1(Mp)$ over $\overline{\mathbb{Q}}$, to the $\overline{\mathbb{Q}}$-points of $D$ over $\operatorname{Spec} A$. A map $\varphi$ from the Hecke polynomial algebra [`ModularCurve.HeckeAlgOne`](def/ModularCurve_X1HeckeModule.html#L16) to endomorphisms of $D$ over $\operatorname{Spec} A$, and for each $s \in \operatorname{Gal}(L/\mathbb{Q})$ a morphism $\tau(s) : D.P \to D.P$ over the twist of $D.\mathrm{toBase}$ by the action of $s$ on $A$. Hypotheses: `hφmul`, each $\varphi(t)$ is additive for the relative group law furnished by `hrep` and `algEquivZeroGroupCut`; `hφpts`, for the Hecke module structure `heckeModuleOneBar` one has $\mathrm{gpts}(t \cdot x) = \mathrm{gpts}(x)$ followed by $\varphi(t)$; `hτ1` and `hτmul`, $\tau(1)$ is the identity and $\tau(ss')$ is $\tau(s)$ followed by $\tau(s')$; `hτφ`, each $\tau(s)$ commutes with each $\varphi(t)$; `hgadd`, `gpts` is additive for the relative group law; `hτpts`, for $\sigma' \in \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ restricting to $s$ on $L$ and all $x$, $\mathrm{gpts}(\sigma' \cdot x)$ is $\operatorname{Spec}(\sigma')$ followed by $\mathrm{gpts}(x)$ followed by $\tau(s^{-1})$.
--
--   **Abel–Jacobi data.** Representability `hDL` of the relative $\mathrm{Pic}^0$ of $X_L$ by $D_L$ with the section $\varepsilon_L$; a morphism $\mathrm{ajL} : X_L \to D_L$ over $\operatorname{Spec} L$; a comparison morphism $k_L : X \times_A \overline{\mathbb{Q}} \to X \times_A L$ compatible with both projections (`hkL₁`, `hkL₂`); a morphism $\overline{\mathrm{aj}} : M_\eta.C \to D.P$ and a $\overline{\mathbb{Q}}$-point $\overline{\varepsilon}$ of $M_\eta.C$. The hypotheses are: `hPL`, the Poincaré bundle of `hDL` is isomorphic to the base change to $L$ of the pullback of the Poincaré bundle of `hrep` along the first projection $D_L \to D$; `hajLε`, $\varepsilon_L$ followed by $\mathrm{ajL}$ is the zero section of $D_L$; `hajL`, for every field $K'$, every $t : \operatorname{Spec} K' \to \operatorname{Spec} L$ and every $K'$-point $x$ of $X_L$, the pullback of the Poincaré bundle of `hDL` along $x$ followed by $\mathrm{ajL}$ is isomorphic to the line bundle of the relative effective Cartier divisor of the point $x$ tensored with the ideal module of the divisor of the point $t$ followed by $\varepsilon_L$, so that $\mathrm{ajL}$ computes the class $[x] - [\varepsilon]$; `hajbar`, $\overline{\mathrm{aj}} = e_\eta$ followed by $k_L$, $\mathrm{ajL}$ and the first projection; `hajbar_over`, $\overline{\mathrm{aj}}$ lies over $M_\eta.\mathrm{toBase}$ followed by $\operatorname{Spec} A \leftarrow \operatorname{Spec}\overline{\mathbb{Q}}$; `hεbar`, $\overline{\varepsilon}$ followed by $e_\eta$ and the first projection is $\varepsilon$ pulled back to $\overline{\mathbb{Q}}$; `hεbar_aj`, $\overline{\varepsilon}$ followed by $\overline{\mathrm{aj}}$ is the zero section; `hpts_aj`, for all $\overline{\mathbb{Q}}$-points $x, s$ of $M_\eta.C$ with $s$ equal to $\varepsilon$ in the above sense, there is a degree-zero divisor $D_v$ equal to $\mathrm{single}(\mathrm{place}\,x, 1) - \mathrm{single}(\mathrm{place}\,s, 1)$ whose class satisfies $\mathrm{gpts}(\mathrm{Pic0.mk}\,D_v) = x$ followed by $\overline{\mathrm{aj}}$.
--
--   **The norm-free abelian subscheme.** A scheme $\mathcal{A}$ with a morphism $a : \mathcal{A} \to \operatorname{Spec} A$ and a morphism $\iota : \mathcal{A} \to D.P$ over $a$, subject to the conjunction `h𝒜` of five clauses: (i) $\iota$ is a closed immersion; (ii) $a$ is proper and smooth and for every algebraically closed field and every morphism from its spectrum to $\operatorname{Spec} A$ the corresponding fibre product is connected; (iii) for every $T$-point $s$ of $\operatorname{Spec} A$, the image of $\mathcal{A}$ under $\iota$ contains the unit of the relative group law and is closed under its multiplication and inversion; (iv) an element $x$ of [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186) lies in [`ModularCurve.normFreePartAt (M * p) p`](def/ModularCurve_X1PrimitiveSpecializationAtP.html#L29) if and only if the $\overline{\mathbb{Q}}$-point $\mathrm{gpts}(x)$ of $D$ factors through $\iota$; (v) the image of $\mathcal{A}$ is stable under every Hecke endomorphism $\varphi(t)$, in the sense that for each $t$ and each $T$-point $x$ of $\mathcal{A}$ there is a $T$-point $z$ of $\mathcal{A}$ with $\iota \circ z$ equal to $\varphi(t) \circ \iota \circ x$.
--
--   **Place data.** A valuation subring $\mathrm{Pl}$ of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $\mathrm{Pl}$ (`hPl`); a ring homomorphism $\rho : A \to \mathrm{Pl}$ whose composite with the inclusion is the structure map $A \to \overline{\mathbb{Q}}$ (`hρ`); a subring $O \le \mathrm{Pl}$ (`hO`) with a ring homomorphism $\rho_O : A \to O$ whose composite with the inclusion is again the structure map (`hρO`); a ring homomorphism $\pi_k : \mathrm{Pl} \to k$ with $A \to k$ equal to $\pi_k \circ \rho$ (`hAlgk`), assumed surjective (`hπk`).
--
--   **Eichler–Shimura hypothesis on $k$-points.** The hypothesis `hES` asserts the existence of a self-map $\Phi_2$ of the set of $k$-points of $D_2$ such that: (a) for all $k$-points $v, v'$ of $D_k$, if $v$ followed by the first projection $D_k \to D$ factors as $w$ followed by $\iota$ for some $w : \operatorname{Spec} k \to \mathcal{A}$ over $\operatorname{Spec} A$, and if $v'$ followed by the first projection equals $v$ followed by the first projection and then by $\varphi(\mathrm{heckeGenOne}\,p)$, then $\nu_2 \circ v' = \Phi_2(\nu_2 \circ v)$; (b) $\Phi_2$ is additive for the relative group law on $D_2$ furnished by `hrep₂`; (c) $\Phi_2$ is bijective.
--
--   **Conclusion.** There exists an additive automorphism $\Phi_2$ of $G.J_E$ such that for every $x \in$ [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186), all $O$-points $z, z'$ of $D$ over $\operatorname{Spec}(\rho_O)$, and all $y, y' \in G.J_s^0$: if $x$ lies in [`ModularCurve.normFreePartAt (M * p) p`](def/ModularCurve_X1PrimitiveSpecializationAtP.html#L29); if the $\overline{\mathbb{Q}}$-point $\mathrm{gpts}(x)$ is $\operatorname{Spec}$ of the inclusion $O \to \overline{\mathbb{Q}}$ followed by $z$; if the $k$-point $\mathrm{pts}(y)$ of $D_k$, followed by the first projection to $D$, is $\operatorname{Spec}$ of the reduction $O \to \mathrm{Pl} \to k$ followed by $z$; if $z'$ is $z$ followed by $\varphi(\mathrm{heckeGenOne}\,p)$; and if $\mathrm{pts}(y')$, followed by the first projection, is the same reduction morphism followed by $z'$; then $(G.\mathrm{proj}\,y')_2 = \Phi_2((G.\mathrm{proj}\,y)_2)$.
--
--   This is the étale-component reading of the Eichler–Shimura relation for $U_p$ on the geometric special fibre at $p$ of the Jacobian of $X_1(Mp)$: the hypothesis on $k$-points of the relative $\mathrm{Pic}^0$ of the étale component is converted into a single additive automorphism of the group $J_E$ which computes, on reductions of norm-free points, the second coordinate of the projection $J_s^0 \to J_I \times J_E$ after applying $U_p$. It is used in the companion statement about the norm-free family, which together with the cusp-component reading gives the triangular shape of $U_p$ on $J_s^0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_addEquiv_proj_snd_eq_of_pts_reduction_heckeGenOne_of_normFreePart_of_eichlerShimura_twoChartModel_x1_mul.lean

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

theorem ModularCurve.XOneP.exists_addEquiv_proj_snd_eq_of_pts_reduction_heckeGenOne_of_normFreePart_of_eichlerShimura_twoChartModel_x1_mul
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

    (hπk : Function.Surjective ⇑πk)

    (hES : ∃ Φ₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₂.toBase → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₂.toBase,

      (∀ (v v' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase),
      (∃ w : Spec (CommRingCat.of k) ⟶ 𝒜, w ≫ a = specMap A k ∧
          v.1 ≫ pullback.fst D.toBase (specMap A k) = w ≫ ι.1) →
      v'.1 ≫ pullback.fst D.toBase (specMap A k) = (v.1 ≫ pullback.fst D.toBase (specMap A k)) ≫ (φ (ModularCurve.heckeGenOne ⟨p, Fact.out⟩)).1 →
        postComp ν₂ v' = Φ₂ (postComp ν₂ v)) ∧

      (∀ x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₂.toBase,
        Φ₂ ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₂.some).mul (𝟙 (Spec (CommRingCat.of k))) x y) =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₂.some).mul (𝟙 (Spec (CommRingCat.of k))) (Φ₂ x) (Φ₂ y)) ∧

      Function.Bijective Φ₂) :

    ∃ Φ₂ : G.JE ≃+ G.JE,
    ∀ (x : ModularCurve.JOne (M * p))
      (z z' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) D.toBase) (y y' : G.J0s),

      x ∈ ModularCurve.normFreePartAt (M * p) p →

      (gpts x).1 = Spec.map (CommRingCat.ofHom O.subtype) ≫ z.1 →

      (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ z.1 →

      z'.1 = z.1 ≫ (φ (ModularCurve.heckeGenOne ⟨p, Fact.out⟩)).1 →

      (pts y').1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ z'.1 →
      (G.proj y').2 = Φ₂ (G.proj y).2 := by sorry
