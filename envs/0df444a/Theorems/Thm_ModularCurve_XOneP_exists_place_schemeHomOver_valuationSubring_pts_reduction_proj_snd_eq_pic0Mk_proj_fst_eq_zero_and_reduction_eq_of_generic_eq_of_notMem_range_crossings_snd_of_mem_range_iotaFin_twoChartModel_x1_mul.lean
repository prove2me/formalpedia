-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_place_schemeHomOver_valuationSubring_pts_reduction_proj_snd_eq_pic0Mk_proj_fst_eq_zero_and_reduction_eq_of_generic_eq_of_notMem_range_crossings_snd_of_mem_range_iotaFin_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_place_schemeHomOver_valuationSubring_pts_reduction_proj_snd_eq_pic0Mk_proj_fst_eq_zero_and_reduction_eq_of_generic_eq_of_notMem_range_crossings_snd_of_mem_range_iotaFin_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/fba95fdb-4d79-5bd3-96d4-c89ae3006129
-- title:
--   Lifting two good C₂-points of X₁(Mp) to Pic⁰
-- statement:
--   Throughout, $p$ is a prime and $M$ a nonzero natural number with $5 \le M$ and $p \nmid M$ (`hM`, `hpM`). The field $L$ is of characteristic zero and is a cyclotomic extension of $\mathbb Q$ for $\{p\}$, with $\zeta \in L$ a primitive $p$-th root of unity (`hζ`). The field $K$ is an intermediate field of $L \subseteq L(\!(q)\!)$ which, by `hK`, equals [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), the subfield of the Laurent series field over $L$ generated over $L$ by the coefficientwise image of the function field of $X_1(Mp)$. The ring $A$ is a discrete valuation domain with fraction field $L$, with $p$ in its maximal ideal (`hAp`), with $\zeta$ in the image of $A$ (`hζA`), and with an $A$-algebra structure on $K$ compatible with the tower $A \to L \to K$. The element $j \in K$ is nonzero and has Laurent expansion the coefficient embedding of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), the $q$-expansion of the modular invariant (`hj`). The relevant integral model is the two-chart model of $K$ over $A$ with distinguished element $j$, glued from the spectra of the subalgebras [`ModularCurve.TwoChart.chartAlgFin A K j`](def/ModularCurve_TwoChartModel.html#L135) and its counterpart at infinity, with structure morphism [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252), assumed proper.
--
--   Special fibre data: $k$ is an algebraically closed field of characteristic $p$ and an $A$-algebra; $C_1 \to \operatorname{Spec} k$ and $C_2 \to \operatorname{Spec} k$ (written $c_1$, $c_2$) are proper, smooth of relative dimension $1$ and geometrically integral; $i_1$, $i_2$ are closed immersions of $C_1$, $C_2$ into the fibre of the two-chart model over $\operatorname{Spec} k$, compatibly with the structure morphisms. The hypothesis `hcover` says that every point of that fibre lies in the image of $i_1$ or of $i_2$; `hred` says that the intersection scheme $C_1 \times_{X_k} C_2$ is reduced, and `hn`, `hn0` say that it has exactly $n$ points with $n > 0$.
--
--   Sections and Picard data: $\varepsilon$ is a section of the two-chart model over $\operatorname{Spec} A$, and $\varepsilon_1$, $\varepsilon_2$ are $k$-points of $C_1$, $C_2$, with `hε₁` requiring that $\varepsilon_1$ followed by $i_1$ be the base change of $\varepsilon$ to $k$. The datum $D$ is a relative $\mathrm{Pic}^0$ designation over $A$ for the two-chart model, that is, a scheme $D.P$ with a structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec} A$ and a zero section; `hrep` asserts that $D$ represents the relative sub-Picard functor cut out by the fibrewise algebraically-trivial condition `algEquivZeroCut` with respect to $\varepsilon$ (a Poincaré rigidified line bundle satisfying that condition, the universal property classifying such bundles by points of $D.\mathrm{toBase}$, and triviality along the zero section), and `hsm`, `hsep` require $D.\mathrm{toBase}$ to be smooth and separated. The hypothesis `hreps` is the corresponding representability statement for the base change of the curve and of $D$ to $k$, and `hPk` requires the Poincaré bundle there to be isomorphic to the base change of the Poincaré bundle of `hrep.some` along the first projection. Similarly $D_1$, $D_2$ are relative $\mathrm{Pic}^0$ designations over $k$ for $c_1$, $c_2$, with representability `hrep₁`, `hrep₂`. The morphism $\nu_2$ goes from $(D.\mathrm{baseChange}\ k).\mathrm{toBase}$ to $D_2.\mathrm{toBase}$ over $k$, and `hν₂` identifies it with restriction of line bundles to $C_2$: for every $k$-scheme $t : T \to \operatorname{Spec} k$ and every $T$-point $a$ of $(D.\mathrm{baseChange}\ k).\mathrm{toBase}$, the pullback of the Poincaré bundle of `hrep₂.some` along $a$ followed by $\nu_2$ is isomorphic to the rigidification, in the sense of `Scheme.Modules.rigidify` along `rigSection c₂ t ε₂` and $\mathrm{pr}_2$, of the pullback along `curveChange i₂.1 i₂.2 t` of the bundle obtained from `hreps` by pulling back along $a$.
--
--   Generic fibre data: with compatible algebra structures $A \to \overline{\mathbb Q}$, $L \to \overline{\mathbb Q}$, the datum $M\eta$ is a curve model over $\overline{\mathbb Q}$ of the function field [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) (the base change to $\overline{\mathbb Q}$, inside $\overline{\mathbb Q}(\!(q)\!)$, of the function field of $X_1(Mp)$), and $e\eta$ is an isomorphism of $M\eta.C$ with the fibre of the two-chart model over $\operatorname{Spec}\overline{\mathbb Q}$ compatible with the structure morphisms (`heη`). The chart preimage is nonempty, and `hMηpin` pins the model to $q$-expansions: for every $a$ in the finite chart algebra, the germ of $a$ along the chart, read in the function field through $M\eta.\mathrm{ffEquiv}$, has Laurent expansion the coefficientwise image under $L \to \overline{\mathbb Q}$ of the Laurent expansion of $a$. The hypothesis `hgal` is Galois equivariance of the bijection between $\overline{\mathbb Q}$-points and places: for $g \in \operatorname{Aut}(\overline{\mathbb Q}/\mathbb Q)$ fixing the image of $L$ pointwise, and $\overline{\mathbb Q}$-points $x$, $x'$ of $M\eta.C$, if $x'$ followed by $e\eta$ and the first projection equals $\operatorname{Spec}(g)$ followed by the same composite applied to $x$, then $M\eta.\mathrm{pointEquivPlace}\,x' = \mathrm{arithmeticGalois}(g) \cdot M\eta.\mathrm{pointEquivPlace}\,x$.
--
--   Group-theoretic dictionaries: $G$ is a [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9), consisting of abelian groups $J0s$, $JI$, $JE$, a subgroup `torus` of $J0s$, and a surjection $\mathrm{proj} : J0s \to JI \times JE$ with kernel `torus`. The bijections `pts`, `ptsI`, `ptsE` identify $J0s$, $JI$, $JE$ with the $k$-points of $(D.\mathrm{baseChange}\ k).\mathrm{toBase}$, $D_1.\mathrm{toBase}$, $D_2.\mathrm{toBase}$; `hadd`, `haddI`, `haddE` require them to be additive in the sense that the Poincaré pullback along a sum is isomorphic to the tensor product of the Poincaré pullbacks; and `hproj` requires that for $x \in J0s$ the first component of $\mathrm{proj}\,x$ correspond, under `ptsI`, to $\mathrm{pts}\,x$ followed by the restriction morphism `RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some`, and the second component to $\mathrm{pts}\,x$ followed by $\nu_2$. On the generic fibre, `gpts` is a bijection between $\mathrm{JOne}(Mp) = \mathrm{Pic}^0_{\overline{\mathbb Q}}$ of the function field and the $\overline{\mathbb Q}$-points of $D.\mathrm{toBase}$, additive for the relative group law of `hrep.some` (`hgadd`). The map $\varphi$ assigns to each element of [`ModularCurve.HeckeAlgOne`](def/ModularCurve_X1HeckeModule.html#L16) an endomorphism of $D.\mathrm{toBase}$ over $A$; `hφmul` makes each $\varphi(t)$ additive for the relative group law, and `hφpts` requires, for the Hecke module structure [`ModularCurve.heckeModuleOneBar (M * p)`](def/ModularCurve_X1HeckeModule.html#L129), that $\mathrm{gpts}(t \cdot x)$ be $\mathrm{gpts}(x)$ followed by $\varphi(t)$.
--
--   Abel–Jacobi data: `hDL` is representability after base change to $L$; $ajL$ is a morphism from the $L$-curve to $(D.\mathrm{baseChange}\ L).\mathrm{toBase}$ over the $L$-curve; $kL$ is a morphism between the fibres over $\overline{\mathbb Q}$ and over $L$ compatible with both projections (`hkL₁`, `hkL₂`); `hPL` is the base-change compatibility of the Poincaré bundle over $L$; `hajLε` says $ajL$ sends the cusp section to the zero section; and `hajL` is the Abel–Jacobi property: for every field $K'$, every $K'$-point $t$ of $\operatorname{Spec} L$ and every point $x$ of the $L$-curve over $t$, the Poincaré bundle pulled back along $x$ followed by $ajL$ is isomorphic to the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of the divisor of the cusp section. The morphism $ajbar : M\eta.C \to D.P$ is defined by `hajbar` as $e\eta$ followed by $kL$, $ajL$ and the first projection, and lies over the base by `hajbar_over`; $\bar\varepsilon$ is a $\overline{\mathbb Q}$-point of $M\eta.C$ lying over the cusp (`hεbar`) and carried by $ajbar$ to the zero section (`hεbar_aj`). Finally `hpts_aj` states that for all $\overline{\mathbb Q}$-points $x$, $s$ of $M\eta.C$ with $s$ the cusp point, there is a degree-zero divisor $Dv = [\text{place of } x] - [\text{place of } s]$ with $\mathrm{gpts}(\mathrm{Pic}^0\text{-class of } Dv)$ equal to $x$ followed by $ajbar$.
--
--   Igusa identifications: $w$ is an integral weight-one form of level $M$ over $k$ (a weight-one modular form on $\Gamma_1(M)$ with an integral $q$-expansion whose reduction in $k$ is nonzero), and [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35) is the associated Igusa function field over $k$. The datum $Mdl_1$ is a curve model of that field over $k$ with an isomorphism $e_1 : Mdl_1.C \cong C_1$ compatible with the structure morphisms (`he₁`), a nonempty chart preimage, and the Gauss pinning `hgauss₁`: for $a$ in the finite chart algebra and power series $x$, $y$ over $A$ with $y$ having nonzero reduction in $k$, if the Laurent expansion of $a$ times that of $y$ equals that of $x$ over $L$, then the germ of $a$ read in the Igusa function field through $Mdl_1.\mathrm{ffEquiv}$ has Laurent expansion the reduction of $x$ divided by the reduction of $y$. The isomorphism $\theta_1 : JI \cong \mathrm{Pic}^0_k$ of the Igusa function field is pinned by `hθpin₁`: whenever the Poincaré pullback along $\mathrm{ptsI}\,g$ is isomorphic to the line bundle of a $k$-point $x$ of $C_1$ tensored with the ideal module of $\varepsilon_1$, then $\theta_1 g$ is the class of $[\text{place of } x] - [\text{place of } \varepsilon_1]$, computed through $e_1^{-1}$ and $Mdl_1.\mathrm{pointEquivPlace}$. The semilinear automorphism $frobIg$ of the Igusa function field over $k$ raises every Laurent coefficient to the $p$-th power (`hfrobIg`).
--
--   The subscheme-of-$D$ data: $\mathcal A \to \operatorname{Spec} A$ (written $a$) together with a closed immersion $\iota$ of $\mathcal A$ into $D.\mathrm{toBase}$ over $A$ (`h𝒜cl`), with $a$ proper (`h𝒜pr`) and smooth (`h𝒜sm`), with all geometric fibres connected (`h𝒜conn`), stable under the relative group law in the sense of `h𝒜grp` (the unit, products and inverses of points factoring through $\iota$ again factor through $\iota$), characterised on the generic fibre by `h𝒜gen` (a class $x \in \mathrm{JOne}(Mp)$ lies in the subgroup [`ModularCurve.normFreePartAt (M * p) p`](def/ModularCurve_X1PrimitiveSpecializationAtP.html#L29) precisely when $\mathrm{gpts}\,x$ factors through $\iota$), and stable under each $\varphi(t)$ (`h𝒜hecke`).
--
--   The place of $\overline{\mathbb Q}$: $Pl$ is a valuation subring of $\overline{\mathbb Q}$ with $p$ a nonunit of $Pl$ (`hPl`), $\rho : A \to Pl$ is a ring homomorphism inducing the structure map $A \to \overline{\mathbb Q}$ (`hρ`), $O$ is a subring of $\overline{\mathbb Q}$ contained in $Pl$ with a homomorphism $\rho_O : A \to O$ inducing the same structure map (`hO`, `hρO`), and $\pi_k : Pl \to k$ is a surjective ring homomorphism (`hπk`) with $\pi_k \circ \rho$ the structure map $A \to k$ (`hAlgk`).
--
--   The level-$p$ involution and the second component: $\sigma$ is an $L$-algebra automorphism of $K$ with $\sigma j$ having Laurent expansion the coefficient embedding of [`ModularCurve.qExpand ℚ p ModularCurve.jq`](def/ModularCurve_X0.html#L25) (`hσj`), preserving the finite chart algebra in both directions (`hσfin`), and satisfying `hσW`: for every valuation subring $W_0$ of $K$ characterised by the Gauss condition that $f \in W_0$ if and only if $f = x/y$ for power series $x$, $y$ over $A$ with $y$ of nonzero reduction, the pullback of $W_0$ along $\sigma$ differs from $W_0$ and contains $P(j)$ and $P(j)^{-1}$ for every polynomial $P$ over $A$ with nonzero reduction. The datum $Mdl_2$ is a curve model over $k$ of the same Igusa function field with an isomorphism $e_2 : Mdl_2.C \cong C_2$ compatible with the structure morphisms (`he₂`), a nonempty chart preimage, and the $\sigma$-twisted Gauss pinning `hgauss₂` (as `hgauss₁`, but with the Laurent expansion of $\sigma(a)$ in place of that of $a$). The isomorphism $\theta_2 : JE \cong \mathrm{Pic}^0_k$ of the Igusa function field is pinned by `hθpin₂`, the exact analogue of `hθpin₁` for $C_2$, $\varepsilon_2$, $D_2$, $e_2$ and $Mdl_2$.
--
--   Under these hypotheses the conclusion is the following. Let $c$, $c'$ be $k$-points of $C_2$ (sections of $c_2$) such that the image point of $c$ avoids the range of the projection $C_1 \times_{X_k} C_2 \to C_2$, the image of $c$ under $i_2$ followed by the first projection lies in the range of the finite chart immersion [`ModularCurve.TwoChart.ιFin A K j`](def/ModularCurve_TwoChartModel.html#L231), and likewise for $c'$. Then there exist places $P$, $P'$ of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) over $\overline{\mathbb Q}$, a $Pl$-point $zz$ of $D.\mathrm{toBase}$ over $\operatorname{Spec}(\rho)$, an element $t \in J0s$, a witness $hDv$ that $[P] - [P']$ has degree zero, and a witness $hdz$ that the difference of the places attached by $Mdl_2.\mathrm{pointEquivPlace}$ to $c \circ e_2^{-1}$ and $c' \circ e_2^{-1}$ has degree zero, such that:
--
--   (i) for every place $Q$ in the support of $[P] - [P']$ there are a $Pl$-point $\xi$ of the two-chart model over $\operatorname{Spec}(\rho)$ and a $k$-point $d$ of $C_2$ with: $\operatorname{Spec}(Pl \hookrightarrow \overline{\mathbb Q})$ followed by $\xi$ equal to the $\overline{\mathbb Q}$-point $M\eta.\mathrm{pointEquivPlace}^{-1}(Q)$ followed by $e\eta$ and the first projection; $d$ followed by $i_2$ and the first projection equal to $\operatorname{Spec}(\pi_k)$ followed by $\xi$; the image point of $d$ avoiding the range of the projection $C_1 \times_{X_k} C_2 \to C_2$; and the image of $d$ under $i_2$ followed by the first projection lying in the range of the finite chart immersion;
--
--   (ii) $\mathrm{gpts}$ of the class of $[P] - [P']$ equals $\operatorname{Spec}(Pl \hookrightarrow \overline{\mathbb Q})$ followed by $zz$;
--
--   (iii) $\mathrm{pts}\,t$ followed by the projection $D.P \times_{\operatorname{Spec} A} \operatorname{Spec} k \to D.P$ equals $\operatorname{Spec}(\pi_k)$ followed by $zz$;
--
--   (iv) $\theta_2$ of the second component of $\mathrm{proj}\,t$ equals the class of $[\text{place of } c] - [\text{place of } c']$ in $\mathrm{Pic}^0_k$ of the Igusa function field, and the first component of $\mathrm{proj}\,t$ is zero;
--
--   (v) there is a $Pl$-point $\xi$ of the two-chart model over $\operatorname{Spec}(\rho)$ whose generic fibre, that is $\operatorname{Spec}(Pl \hookrightarrow \overline{\mathbb Q})$ followed by $\xi$, is the $\overline{\mathbb Q}$-point attached to $P$ through $M\eta.\mathrm{pointEquivPlace}^{-1}$, $e\eta$ and the first projection, and whose reduction satisfies: $c$ followed by $i_2$ and the first projection equals $\operatorname{Spec}(\pi_k)$ followed by $\xi$;
--
--   (vi) the same statement for $P'$ and $c'$.
--
--   This is the transfer step, on the non-Gauss component $C_2$ of the special fibre of the Deligne–Rapoport style model of $X_1(Mp)$ over a discrete valuation ring containing $\zeta_p$, from a difference of two $k$-points of $C_2$ lying off the crossings and inside the finite chart to a degree-zero divisor on the generic fibre: the class of $[P]-[P']$ is realised by a $Pl$-integral point of the relative $\mathrm{Pic}^0$ whose reduction is the given point $t$ of the special fibre, whose component in $J_I$ vanishes and whose component in $J_E$ is the prescribed Igusa class, with the additional record that $P$ and $P'$ are the generic places of integral points reducing to $c$ and $c'$. It is used in the subsequent comparison of the Hecke and diamond actions with the Frobenius on the $C_2$-component.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_place_schemeHomOver_valuationSubring_pts_reduction_proj_snd_eq_pic0Mk_proj_fst_eq_zero_and_reduction_eq_of_generic_eq_of_notMem_range_crossings_snd_of_mem_range_iotaFin_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP
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
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
set_option maxHeartbeats 400000 in

theorem ModularCurve.XOneP.exists_place_schemeHomOver_valuationSubring_pts_reduction_proj_snd_eq_pic0Mk_proj_fst_eq_zero_and_reduction_eq_of_generic_eq_of_notMem_range_crossings_snd_of_mem_range_iotaFin_twoChartModel_x1_mul
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

    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))
    (φ : ModularCurve.HeckeAlgOne → SchemeHomOver D.toBase D.toBase)
    (hφmul : ∀ (t : ModularCurve.HeckeAlgOne) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s x y) (φ t) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
          (NeronModelInfra.schemeHomOverComp x (φ t)) (NeronModelInfra.schemeHomOverComp y (φ t)))
    (hφpts : letI := ModularCurve.heckeModuleOneBar (M * p)
      ∀ (t : ModularCurve.HeckeAlgOne) (x : ModularCurve.JOne (M * p)), (gpts (t • x)).1 = (gpts x).1 ≫ (φ t).1)

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

    (θ₁ : G.JI ≃+ AlgebraicCurve.Pic0 k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hθpin₁ : ∀ (g : G.JI) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
      Nonempty ((hrep₁.some.poincare.pullbackAlong (ptsI g)).L ≅
        (RelEffCartierDiv.ofPoint c₁ x.1 x.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₁ ε₁.1 ε₁.2).idealModule) →
      ∃ Dv : Divisor.degZero (K := k) (F := ↥(ModularCurve.igusaFunctionFieldX1C k M w)),
        (Dv : Divisor k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) =
          Finsupp.single (Mdl₁.pointEquivPlace ⟨x.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact x.2⟩) 1 -
            Finsupp.single (Mdl₁.pointEquivPlace ⟨ε₁.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact ε₁.2⟩) 1 ∧
        θ₁ g = Pic0.mk Dv)

    (frobIg : SemilinearAut k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hfrobIg : ∀ (x : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (n : ℤ),
      ((frobIg • x : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k).coeff n = ((x : LaurentSeries k).coeff n) ^ p)

    (𝒜 : Scheme.{0}) (a : 𝒜 ⟶ Spec (CommRingCat.of A)) (ι : SchemeHomOver a D.toBase)

    (h𝒜cl : IsClosedImmersion ι.1)

    (h𝒜pr : IsProper a) (h𝒜sm : Smooth a)
    (h𝒜conn : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)),
        ConnectedSpace ↥(pullback a s))

    (h𝒜grp : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)),
        (∃ o : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp o ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).one s) ∧
        (∀ x y : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
            (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι)) ∧
        (∀ x : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).inv s
            (NeronModelInfra.schemeHomOverComp x ι)))

    (h𝒜gen : ∀ x : ModularCurve.JOne (M * p),
        x ∈ ModularCurve.normFreePartAt (M * p) p ↔
          ∃ y : SchemeHomOver (specMap A (AlgebraicClosure ℚ)) a, y.1 ≫ ι.1 = (gpts x).1)

    (h𝒜hecke : ∀ (t : ModularCurve.HeckeAlgOne) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x : SchemeHomOver s a),
        ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp x ι) (φ t))

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (O : Subring (AlgebraicClosure ℚ)) (hO : O ≤ Pl.toSubring)
    (ρO : A →+* ↥O) (hρO : O.subtype.comp ρO = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ)

    (hπk : Function.Surjective ⇑πk)

    [NeZero p]
    (σ : ↥K ≃ₐ[L] ↥K)
    (hσj : ((σ j : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq))
    (hσfin : ∀ b : ↥K, b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j ↔ σ b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
    (hσW : ∀ W₀ : ValuationSubring ↥K, (∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧ (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) → W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ≠ W₀ ∧ (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 → Polynomial.aeval j P ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ∧ (Polynomial.aeval j P)⁻¹ ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom))
    (Mdl₂ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₂ : Mdl₂.C ≅ C₂)
    (he₂ : e₂.hom ≫ c₂ = Mdl₂.toBase)
    [hne₂ : Nonempty (Scheme.Opens.toScheme ((e₂.hom ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hgauss₂ : ∀ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A), y.map (algebraMap A k) ≠ 0 → ((σ (a : ↥K) : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) → ((Mdl₂.ffEquiv.symm (Mdl₂.C.germToFunctionField ((e₂.hom ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)) (((e₂.hom ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a)))) : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) = HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) / HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k)))
    (θ₂ : G.JE ≃+ AlgebraicCurve.Pic0 k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hθpin₂ : ∀ (g : G.JE) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂), Nonempty ((hrep₂.some.poincare.pullbackAlong (ptsE g)).L ≅ (RelEffCartierDiv.ofPoint c₂ x.1 x.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₂ ε₂.1 ε₂.2).idealModule) → ∃ Dv : Divisor.degZero (K := k) (F := ↥(ModularCurve.igusaFunctionFieldX1C k M w)), (Dv : Divisor k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) = Finsupp.single (Mdl₂.pointEquivPlace ⟨x.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact x.2⟩) 1 - Finsupp.single (Mdl₂.pointEquivPlace ⟨ε₂.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact ε₂.2⟩) 1 ∧ θ₂ g = Pic0.mk Dv) :
    ∀ (c c' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂),

      (∀ t, c.1.base t ∉ Set.range (pullback.snd i₁.1 i₂.1).base) →
      (∀ t, (c.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base t ∈
          Set.range (ModularCurve.TwoChart.ιFin A (↥K) j).base) →
      (∀ t, c'.1.base t ∉ Set.range (pullback.snd i₁.1 i₂.1).base) →
      (∀ t, (c'.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base t ∈
          Set.range (ModularCurve.TwoChart.ιFin A (↥K) j).base) →
      ∃ (P P' : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)))
        (zz : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (t : G.J0s)
        (hDv : Finsupp.single P (1 : ℤ) - Finsupp.single P' 1 ∈
          Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.x1FunctionFieldBar (M * p))))
        (hdz : Finsupp.single (Mdl₂.pointEquivPlace ⟨c.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact c.2⟩) (1 : ℤ) -
            Finsupp.single (Mdl₂.pointEquivPlace ⟨c'.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact c'.2⟩) 1 ∈
          Divisor.degZero (K := k) (F := ↥(ModularCurve.igusaFunctionFieldX1C k M w))),

        (∀ Q ∈ ((Finsupp.single P (1 : ℤ) - Finsupp.single P' 1 : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)))).support,
          ∃ (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j))
            (d : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂),
            Spec.map (CommRingCat.ofHom Pl.subtype) ≫ ξ.1 =
              (Mη.pointEquivPlace.symm Q).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ∧
            d.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
              Spec.map (CommRingCat.ofHom πk) ≫ ξ.1 ∧
            (∀ t, d.1.base t ∉ Set.range (pullback.snd i₁.1 i₂.1).base) ∧
            ∀ t, (d.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base t ∈
              Set.range (ModularCurve.TwoChart.ιFin A (↥K) j).base) ∧

        (gpts (Pic0.mk ⟨_, hDv⟩)).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ zz.1 ∧

        (pts t).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ zz.1 ∧

        θ₂ (G.proj t).2 = Pic0.mk ⟨_, hdz⟩ ∧ (G.proj t).1 = 0 ∧

        (∃ ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j),
          Spec.map (CommRingCat.ofHom Pl.subtype) ≫ ξ.1 =
            (Mη.pointEquivPlace.symm P).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ∧
          c.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ ξ.1) ∧
        (∃ ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j),
          Spec.map (CommRingCat.ofHom Pl.subtype) ≫ ξ.1 =
            (Mη.pointEquivPlace.symm P').1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ∧
          c'.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ ξ.1) := by sorry
