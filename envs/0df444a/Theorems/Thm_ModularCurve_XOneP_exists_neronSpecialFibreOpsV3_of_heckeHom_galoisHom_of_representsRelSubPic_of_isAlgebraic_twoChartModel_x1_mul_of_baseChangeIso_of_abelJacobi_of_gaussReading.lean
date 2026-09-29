-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_neronSpecialFibreOpsV3_of_heckeHom_galoisHom_of_representsRelSubPic_of_isAlgebraic_twoChartModel_x1_mul_of_baseChangeIso_of_abelJacobi_of_gaussReading
-- name    : ModularCurve.XOneP.exists_neronSpecialFibreOpsV3_of_heckeHom_galoisHom_of_representsRelSubPic_of_isAlgebraic_twoChartModel_x1_mul_of_baseChangeIso_of_abelJacobi_of_gaussReading
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/8fa107ab-0283-57bd-8999-b4f5d8f126eb
-- title:
--   Hecke, diamond and inertia operators on the Néron special fibre of J₁(Mp)
-- statement:
--   Throughout, $\pi$ denotes the morphism [`ModularCurve.TwoChart.modelTo A (↥K) j`](def/ModularCurve_TwoChartModel.html#L252) from the two-chart model $X =$ [`ModularCurve.TwoChartModel A (↥K) j`](def/ModularCurve_TwoChartModel.html#L229) to $\operatorname{Spec} A$, and $X_k$, $X_L$, $X_{\bar{\mathbb Q}}$ its base changes along `specMap`.
--
--   **Arithmetic data.** A prime $p$ and a natural number $M$ with $5 \le M$ and $p \nmid M$; a field $L$ of characteristic zero which is a cyclotomic extension of $\mathbb Q$ of type $\{p\}$, together with $\zeta \in L$ a primitive $p$-th root of unity; an intermediate field $K$ of $L \subset \mathrm{LaurentSeries}\,L$ with $K =$ [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. $K$ is generated over $L$ inside $L((q))$ by the coefficientwise image of the function field of $X_1(Mp)$, realised as an intermediate field of $\mathbb Q \subset \mathrm{LaurentSeries}\,\mathbb Q$; a discrete valuation domain $A$ with $L$ as its fraction field, such that $p$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A$; an $A$-algebra structure on $K$ compatible with $A \to L \to K$; and an element $j \in K$, nonzero, whose Laurent expansion is the coefficientwise image in $L((q))$ of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular invariant.
--
--   **Geometric special fibre.** An algebraically closed field $k$ of characteristic $p$, an $A$-algebra, such that every $x \in k$ satisfies $x^{p^n} = x$ for some $n > 0$; two proper, geometrically integral $k$-schemes $c_1 : C_1 \to \operatorname{Spec} k$ and $c_2 : C_2 \to \operatorname{Spec} k$, smooth of relative dimension $1$; closed immersions $i_1 : C_1 \to X_k$, $i_2 : C_2 \to X_k$ over $k$ whose images cover every point of $X_k$ (`hcover`); the scheme $C_1 \times_{X_k} C_2$ is reduced and its underlying set has cardinality $n$, with $n > 0$.
--
--   **Sections.** A section $\varepsilon$ of $\pi$ over $\operatorname{Spec} A$, sections $\varepsilon_1$ of $c_1$ and $\varepsilon_2$ of $c_2$, with $\varepsilon_1$ followed by $i_1$ equal to the base change of $\varepsilon$ to $k$ (`hε₁`).
--
--   **Relative Picard data.** A designation $D$ for $\pi$, i.e. a scheme $D.P$ with a structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec} A$ and a zero section; a witness `hrep` (as a nonempty type) that $D$ represents the functor of rigidified line bundles on $X$ relative to $\varepsilon$ satisfying the condition `FibrewiseAlgEquivZero`, with Poincaré bundle $\mathcal P$ and the universal property that every such rigidified bundle over a base $T$ is induced by a unique $T$-point of $D.P$, the pullback along the zero section being trivial; $D.\mathrm{toBase}$ is smooth and separated. A witness `hreps` of the same representability for $X_k/k$ with the section $\varepsilon_k$ and designation $D \times_A k$; an isomorphism (`hPk`) of its Poincaré bundle with the base change to $k$ of the pullback of $\mathcal P$ along the first projection $D \times_A k \to D.P$. Designations $D_1$ for $c_1$ and $D_2$ for $c_2$ with representability witnesses `hrep₁`, `hrep₂`. A $k$-morphism $\nu_2 : (D\times_A k).\mathrm{toBase} \to D_2.\mathrm{toBase}$ such that (`hν₂`) for every $k$-scheme $t : T \to \operatorname{Spec} k$ and every $T$-point $a$ of $D\times_A k$ the pullback of the Poincaré bundle of `hrep₂` along $a$ followed by $\nu_2$ is isomorphic to the rigidification along `rigSection c₂ t ε₂` and `pullback.snd c₂ t` — tensoring with the pullback of the dual of the restriction along that section — of the restriction along `curveChange i₂.1 i₂.2 t` of the pullback of the Poincaré bundle of `hreps` along $a$; thus $\nu_2$ is the Picard pullback along $i_2$ normalised at $\varepsilon_2$.
--
--   **Generic-fibre regularity.** $\pi$ is proper; $A$ and $L$ are algebras over $\mathrm{AlgebraicClosure}\,\mathbb Q$ in a compatible tower; $X_L \to \operatorname{Spec} L$ is smooth of relative dimension $1$ and geometrically integral; $\mathrm{pullback.snd}\,D.\mathrm{toBase}\,(\mathrm{specMap}\,A\,L)$ is proper and geometrically connected.
--
--   **Geometric generic curve model.** A curve model $M_\eta$ over $\mathrm{AlgebraicClosure}\,\mathbb Q$ of the function field [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) (a proper smooth integral curve with an identification of its function field and a bijection between its closed points and the places); an isomorphism $e_\eta : M_\eta.C \to X_{\bar{\mathbb Q}}$ compatible with the structure morphisms (`heη`); nonemptiness of the preimage under $e_\eta$ followed by the first projection of the image of the finite chart [`ModularCurve.TwoChart.ιFin A (↥K) j`](def/ModularCurve_TwoChartModel.html#L231); the pinning hypothesis `hMηpin`, that for every element $a$ of the finite chart algebra [`ModularCurve.TwoChart.chartAlgFin A (↥K) j`](def/ModularCurve_TwoChartModel.html#L135) the element of `x1FunctionFieldBar (M * p)` obtained by transporting the germ of $a$ on that open set through the function-field identification of $M_\eta$ has Laurent expansion equal to the coefficientwise image under $L \to \bar{\mathbb Q}$ of the expansion of $a$ in $L((q))$; and the equivariance hypothesis `hgal`, that for every $\mathbb Q$-automorphism $g$ of $\bar{\mathbb Q}$ fixing the image of $L$ pointwise and all $\bar{\mathbb Q}$-points $x, x'$ of $M_\eta.C$, if $x'$ followed by $e_\eta$ and the first projection equals $\operatorname{Spec}(g)$ followed by that composite for $x$, then the place attached to $x'$ is the image of the place attached to $x$ under the action of [`ModularCurve.arithmeticGalois (ModularCurve.x1FunctionField (M * p)) g`](def/ModularCurve_ArithmeticGalois.html#L54).
--
--   **Hecke inputs.** `hin : ModularCurve.HeckeDiamondInputsAll (M * p)` (the Hecke inputs at each prime over $\bar{\mathbb Q}$, and for each $d$ coprime to $Mp$ a diamond automorphism of the function field together with a base-changed automorphism of its $\bar{\mathbb Q}$-form) and `hcomm : ModularCurve.HeckeDiamondCommuteBar (M * p)` (the generators of the Hecke–diamond family on the $\bar{\mathbb Q}$-form commute).
--
--   **Galois action on $A$.** A multiplicative semiring action of $L \simeq_{\mathbb Q} L$ on $A$ with $\mathrm{algebraMap}\,A\,L(s \cdot a) = s(\mathrm{algebraMap}\,A\,L\,a)$.
--
--   **Points dictionaries on the special fibre.** A structure $G$ of type [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9): abelian groups $G.J0s$, $G.JI$, $G.JE$, a subgroup $G.\mathrm{torus} \le G.J0s$ and a surjection $G.\mathrm{proj} : G.J0s \to G.JI \times G.JE$ with kernel $G.\mathrm{torus}$. Bijections $\mathrm{pts}$, $\mathrm{ptsI}$, $\mathrm{ptsE}$ of $G.J0s$, $G.JI$, $G.JE$ with the $k$-points of $D\times_A k$, $D_1$, $D_2$ respectively; additivity hypotheses `hadd`, `haddI`, `haddE`, each saying that the pullback of the relevant Poincaré bundle along the point attached to $a+b$ is isomorphic to the tensor product of the pullbacks along the points attached to $a$ and to $b$; and `hproj`, saying that for every $x \in G.J0s$ the point attached to the first component of $G.\mathrm{proj}\,x$ is $\mathrm{pts}\,x$ followed by `RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some`, and the point attached to the second component is $\mathrm{pts}\,x$ followed by $\nu_2$.
--
--   **Generic dictionary and operators.** A bijection $\mathrm{gpts}$ of [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186) — the degree-zero divisor classes of `x1FunctionFieldBar (M * p)` over $\bar{\mathbb Q}$ — with the $\bar{\mathbb Q}$-points of $D$; a map $\varphi$ from [`ModularCurve.HeckeAlgOne`](def/ModularCurve_X1HeckeModule.html#L16) $= \mathbb Z[X_i : i \in \mathrm{Primes} \sqcup \mathbb N]$ to endomorphisms of $D$ over $\operatorname{Spec} A$; for each $s \in L \simeq_{\mathbb Q} L$ a morphism $\tau(s) : D.P \to D.P$ semilinear over the induced automorphism of $A$. These satisfy: each $\varphi(t)$ is additive for the relative group law attached to `hrep.some` (`hφmul`); with the Hecke module structure [`ModularCurve.heckeModuleOneBar (M * p)`](def/ModularCurve_X1HeckeModule.html#L129), $\mathrm{gpts}(t \cdot x) = \mathrm{gpts}(x)$ followed by $\varphi(t)$ (`hφpts`); $\tau(1)$ is the identity and $\tau(ss')$ is $\tau(s)$ followed by $\tau(s')$; each $\tau(s)$ commutes with each $\varphi(t)$; $\mathrm{gpts}$ is additive for the relative group law (`hgadd`); and (`hτpts`) for $\sigma' \in \bar{\mathbb Q} \simeq_{\mathbb Q} \bar{\mathbb Q}$ restricting on $L$ to $s$, $\mathrm{gpts}(\sigma' \cdot x) = \operatorname{Spec}(\sigma')$ followed by $\mathrm{gpts}(x)$ followed by $\tau(s^{-1})$.
--
--   **Abel–Jacobi normalisation.** A representability witness `hDL` for $X_L/L$ with section $\varepsilon_L$ and designation $D\times_A L$, together with an isomorphism (`hPL`) of its Poincaré bundle with the base change to $L$ of the pullback of $\mathcal P$ along the first projection; a morphism $\mathrm{ajL}$ from $X_L$ to $(D \times_A L).\mathrm{toBase}$ over $L$ with $\varepsilon_L$ followed by $\mathrm{ajL}$ equal to the zero section (`hajLε`), and satisfying the Abel–Jacobi property `hajL`: for every field $K'$, every morphism $t : \operatorname{Spec} K' \to \operatorname{Spec} L$ and every point $x$ of $X_L$ over $t$, the pullback of the Poincaré bundle of `hDL` along $x$ followed by $\mathrm{ajL}$ is isomorphic to the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of the divisor cut out by $t$ followed by $\varepsilon_L$; a morphism $k_L : X_{\bar{\mathbb Q}} \to X_L$ compatible with both projections (`hkL₁`, `hkL₂`); a morphism $\overline{\mathrm{aj}} : M_\eta.C \to D.P$ equal to $e_\eta$ followed by $k_L$, $\mathrm{ajL}$ and the first projection, lying over $M_\eta.\mathrm{toBase}$ followed by $\mathrm{specMap}\,A\,\bar{\mathbb Q}$; a $\bar{\mathbb Q}$-point $\bar\varepsilon$ of $M_\eta.C$ which corresponds to $\varepsilon$ under $e_\eta$ and the first projection (`hεbar`) and whose image under $\overline{\mathrm{aj}}$ is the zero section (`hεbar_aj`); and `hpts_aj`: for all $\bar{\mathbb Q}$-points $x, s$ of $M_\eta.C$ with $s$ satisfying the same cusp compatibility as $\bar\varepsilon$, there is a degree-zero divisor $Dv$ equal to $[\,\text{place of } x\,] - [\,\text{place of } s\,]$ with $\mathrm{gpts}$ of its class equal to $x$ followed by $\overline{\mathrm{aj}}$.
--
--   **Gauss reading of the first component.** A form $w$ of type [`ModularCurve.IntegralWeightOneForm k M`](def/ModularCurve_IgusaFunctionFieldX1.html#L16) (a weight-one modular form on $\Gamma_1(M)$ with an integral $q$-expansion whose reduction in $k$ is nonzero); a curve model $\mathrm{Mdl}_1$ over $k$ of the Igusa function field [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35); an isomorphism $e_1 : \mathrm{Mdl}_1.C \cong C_1$ over $k$ (`he₁`); nonemptiness of the corresponding chart preimage; and `hgauss₁`: for every $a$ in the finite chart algebra and all power series $x, y$ over $A$ with $y$ having nonzero reduction in $k$, if the Laurent expansion of $a$ times the image of $y$ equals the image of $x$ over $L$, then the element of the Igusa function field obtained by transporting the germ of $a$ along $e_1$ followed by $i_1$ and the first projection has Laurent expansion the quotient of the reductions of $x$ and $y$ in $k[[q]]$.
--
--   **Cusp position and cusp equivariance.** No point of the image of the cusp section $\varepsilon_k$ lies in the image of $i_2$ (`hεC₂`); and `hεgal`: whenever $w_s$ is an endomorphism of the two-chart model semilinear over $s \in L \simeq_{\mathbb Q} L$, $\rho_s$ is a ring automorphism of the finite chart algebra acting on Laurent expansions by coefficientwise $s$, and $w_s$ restricts to $\rho_s$ on the finite chart, then $\varepsilon$ followed by $w_s$ equals $\operatorname{Spec}(s)$ followed by $\varepsilon$.
--
--   **Conclusion.** There exists an operator package $O$ of type [`ModularCurve.JOneP.NeronSpecialFibreOpsV3 G`](def/ModularCurve_JOnePOpsV3.html#L13) — Hecke operators on $G.J0s$, $G.JI$, $G.JE$ compatible along $G.\mathrm{proj}$ for $\ell \ne p$, a diamond action $\mathrm{diamondP}$ of $(\mathbb Z/p)^\times$ by automorphisms of $G.J0s$, operators $\mathrm{diamondN}$, an involution $w$, an inertia action $\mathrm{inertia}$ of $(\mathbb Z/p)^\times$, endomorphisms $\mathrm{verI}$, $\mathrm{frobE}$, $\mathrm{diamondNI}$, with commutation of the Hecke operators with one another and with $\mathrm{diamondP}$ and $\mathrm{inertia}$, and triviality of $\mathrm{diamondP}$ and $\mathrm{inertia}$ on $G.\mathrm{torus}$ — such that, writing $\mathrm{pr}_1$ for the projection $D \times_A k \to D.P$, the following seven statements hold.
--
--   1. For every prime $\ell$ and every $y \in G.J0s$: $\mathrm{pts}(O.\mathrm{hecke}\,\ell\,y)$ followed by $\mathrm{pr}_1$ equals $\mathrm{pts}(y)$ followed by $\mathrm{pr}_1$ and then by $\varphi(\mathrm{heckeGenOne}\,\ell)$.
--
--   2. For every $b \in (\mathbb Z/p)^\times$ and every $d \in \mathbb N$ coprime to $Mp$ with $d \equiv 1 \pmod M$ and $d \equiv b \pmod p$, and every $y$: $\mathrm{pts}(O.\mathrm{diamondP}\,b\,y)$ followed by $\mathrm{pr}_1$ equals $\mathrm{pts}(y)$ followed by $\mathrm{pr}_1$ and then by $\varphi(\mathrm{diamondGen}\,d)$.
--
--   3. For every $d$ coprime to $Mp$ with $d \equiv 1 \pmod p$ and every $y$: $\mathrm{pts}(O.\mathrm{diamondN}\,d\,y)$ followed by $\mathrm{pr}_1$ equals $\mathrm{pts}(y)$ followed by $\mathrm{pr}_1$ and then by $\varphi(\mathrm{diamondGen}\,d)$.
--
--   4. For every $b \in (\mathbb Z/p)^\times$ and every $s \in L \simeq_{\mathbb Q} L$ with $s(\zeta) = \zeta^{\,\mathrm{val}(b)}$, and every $y$: $\mathrm{pts}(O.\mathrm{inertia}\,b\,y)$ followed by $\mathrm{pr}_1$ equals $\mathrm{pts}(y)$ followed by $\mathrm{pr}_1$ and then by $\tau(s)$.
--
--   5. There are additive maps $\mathrm{diamondPI}(b) : G.JI \to G.JI$ and $\mathrm{diamondPE}(b) : G.JE \to G.JE$, for $b \in (\mathbb Z/p)^\times$, with $G.\mathrm{proj}(O.\mathrm{diamondP}\,b\,x) = (\mathrm{diamondPI}(b)\,(G.\mathrm{proj}\,x)_1,\ \mathrm{diamondPE}(b)\,(G.\mathrm{proj}\,x)_2)$ for all $x$.
--
--   6. There are additive maps $\mathrm{diamondNE}(d) : G.JE \to G.JE$, for $d \in \mathbb N$, such that for every $d$ coprime to $Mp$ and every $x$, $G.\mathrm{proj}(O.\mathrm{diamondN}\,d\,x) = (O.\mathrm{diamondNI}\,d\,(G.\mathrm{proj}\,x)_1,\ \mathrm{diamondNE}(d)\,(G.\mathrm{proj}\,x)_2)$.
--
--   7. There are additive maps $\mathrm{inertiaI}(b) : G.JI \to G.JI$ and $\mathrm{inertiaE}(b) : G.JE \to G.JE$ with $G.\mathrm{proj}(O.\mathrm{inertia}\,b\,x) = (\mathrm{inertiaI}(b)\,(G.\mathrm{proj}\,x)_1,\ \mathrm{inertiaE}(b)\,(G.\mathrm{proj}\,x)_2)$ for all $x$.
--
--   No clause about the Hecke operator at $\ell = p$ along $G.\mathrm{proj}$ is asserted beyond the compatibility for $\ell \ne p$ recorded inside the operator structure.
--
--   This is the operator layer of the description of the Néron special fibre of $J_1(Mp)$ at $p$: the Hecke operators, the two families of diamond operators, and the action of inertia on the group of $k$-points of the special fibre are produced as the reductions of the Abel–Jacobi-normalised endomorphisms $\varphi$ and semilinear automorphisms $\tau$ of the relative $\mathrm{Pic}^0$ over $A$, and are shown to descend along the projection to the Jacobians of the two components of the geometric special fibre. It feeds the statement on $q$-expansion semistable specialisation with diamond operators used in the level-lowering step at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_neronSpecialFibreOpsV3_of_heckeHom_galoisHom_of_representsRelSubPic_of_isAlgebraic_twoChartModel_x1_mul_of_baseChangeIso_of_abelJacobi_of_gaussReading.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
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
import Definitions.Def_ModularCurve_JOnePOpsV3
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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.exists_neronSpecialFibreOpsV3_of_heckeHom_galoisHom_of_representsRelSubPic_of_isAlgebraic_twoChartModel_x1_mul_of_baseChangeIso_of_abelJacobi_of_gaussReading
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
    (hk : ∀ x : k, ∃ n : ℕ, 0 < n ∧ x ^ p ^ n = x)
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
      ε.1 ≫ ws = Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)) ≫ ε.1) :
    ∃ O : ModularCurve.JOneP.NeronSpecialFibreOpsV3 G,

      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (y : G.J0s),
        (pts (O.hecke ℓ y)).1 ≫ pullback.fst D.toBase (specMap A k) =
          ((pts y).1 ≫ pullback.fst D.toBase (specMap A k)) ≫ (φ (ModularCurve.heckeGenOne ⟨ℓ, hℓ⟩)).1) ∧
      (∀ (b : (ZMod p)ˣ) (d : ℕ), d.Coprime (M * p) → (d : ZMod M) = 1 → (d : ZMod p) = (b : ZMod p) →
        ∀ y : G.J0s,
          (pts (O.diamondP b y)).1 ≫ pullback.fst D.toBase (specMap A k) =
            ((pts y).1 ≫ pullback.fst D.toBase (specMap A k)) ≫ (φ (ModularCurve.diamondGen d)).1) ∧
      (∀ d : ℕ, d.Coprime (M * p) → (d : ZMod p) = 1 → ∀ y : G.J0s,
        (pts (O.diamondN d y)).1 ≫ pullback.fst D.toBase (specMap A k) =
          ((pts y).1 ≫ pullback.fst D.toBase (specMap A k)) ≫ (φ (ModularCurve.diamondGen d)).1) ∧

      (∀ (b : (ZMod p)ˣ) (s : L ≃ₐ[ℚ] L), s ζ = ζ ^ (b : ZMod p).val → ∀ y : G.J0s,
        (pts (O.inertia b y)).1 ≫ pullback.fst D.toBase (specMap A k) =
          ((pts y).1 ≫ pullback.fst D.toBase (specMap A k)) ≫ (τ s).1) ∧

      (∃ (diamondPI : (ZMod p)ˣ → (G.JI →+ G.JI)) (diamondPE : (ZMod p)ˣ → (G.JE →+ G.JE)),
        ∀ (b : (ZMod p)ˣ) (x : G.J0s), G.proj (O.diamondP b x) = (diamondPI b (G.proj x).1, diamondPE b (G.proj x).2)) ∧
      (∃ diamondNE : ℕ → (G.JE →+ G.JE),
        ∀ (d : ℕ) (x : G.J0s), d.Coprime (M * p) → G.proj (O.diamondN d x) = (O.diamondNI d (G.proj x).1, diamondNE d (G.proj x).2)) ∧
      (∃ (inertiaI : (ZMod p)ˣ → (G.JI →+ G.JI)) (inertiaE : (ZMod p)ˣ → (G.JE →+ G.JE)),
        ∀ (b : (ZMod p)ˣ) (x : G.J0s), G.proj (O.inertia b x) = (inertiaI b (G.proj x).1, inertiaE b (G.proj x).2)) := by sorry
