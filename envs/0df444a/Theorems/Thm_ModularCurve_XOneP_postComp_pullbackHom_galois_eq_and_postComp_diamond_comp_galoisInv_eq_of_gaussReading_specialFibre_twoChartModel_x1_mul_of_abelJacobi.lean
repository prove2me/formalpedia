-- Prove2me | Theorems.Thm_ModularCurve_XOneP_postComp_pullbackHom_galois_eq_and_postComp_diamond_comp_galoisInv_eq_of_gaussReading_specialFibre_twoChartModel_x1_mul_of_abelJacobi
-- name    : ModularCurve.XOneP.postComp_pullbackHom_galois_eq_and_postComp_diamond_comp_galoisInv_eq_of_gaussReading_specialFibre_twoChartModel_x1_mul_of_abelJacobi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/d1682e2e-0afe-51bb-989a-90db42ac808e
-- title:
--   Galois acts trivially on C₁, through a diamond on C₂
-- statement:
--   **Arithmetic and integral data.** Fix a prime $p$, an integer $M\ge 5$ with $p\nmid M$ ($M\neq 0$), a field $L$ of characteristic zero which is a $\{p\}$-cyclotomic extension of $\mathbb{Q}$, and a primitive $p$-th root of unity $\zeta\in L$. Let $K$ be an intermediate field of $L\subseteq \mathrm{LaurentSeries}\,L$ with `hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`, that is, $K$ is generated over $L$ by the coefficientwise image of the function field of $X_1(Mp)$ inside Laurent series over $L$. Let $A$ be a discrete valuation domain with an $A$-algebra structure on $L$ making $L$ its fraction field, such that $p$ lies in the maximal ideal of $A$ (`hAp`) and $\zeta$ lies in the image of $A$ (`hζA`), with $K$ an $A$-algebra compatibly with $A\to L\to K$. Fix $j\in K$ whose Laurent expansion is the image under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular invariant (`hj`), and with $j\neq 0$. Write $X\to \operatorname{Spec}A$ for [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252), the structure morphism of the two-chart model [`ModularCurve.TwoChartModel A K j`](def/ModularCurve_TwoChartModel.html#L229) (the pushout of the finite and the infinite chart), assumed proper; [`ModularCurve.TwoChart.ιFin A K j`](def/ModularCurve_TwoChartModel.html#L231) denotes the finite chart, the spectrum of the subalgebra [`ModularCurve.TwoChart.chartAlgFin A K j`](def/ModularCurve_TwoChartModel.html#L135) of $K$.
--
--   **The special fibre.** Let $k$ be an algebraically closed $A$-algebra of characteristic $p$ and let $c_1 : C_1\to \operatorname{Spec}k$, $c_2 : C_2\to \operatorname{Spec}k$ be proper, smooth of relative dimension $1$ and geometrically integral. Let $i_1,i_2$ be closed immersions of $C_1$, $C_2$ into the fibre $X_k$ (the pullback of $X$ along $\operatorname{Spec}k\to\operatorname{Spec}A$) commuting with the structure morphisms. The hypotheses `hcover`, `hred`, `hn`, `hn0` require that every point of $X_k$ lie in the image of $i_1$ or of $i_2$, that the pullback of $i_1$ and $i_2$ be reduced, and that the number of its points be $n>0$.
--
--   **Sections.** Let $\varepsilon$ be a section of $X\to\operatorname{Spec}A$ and $\varepsilon_1,\varepsilon_2$ sections of $c_1,c_2$, with `hε₁` asserting that $\varepsilon_1$ followed by $i_1$ is the base change of $\varepsilon$ to $k$.
--
--   **Relative Picard data.** Let $D$ be a `RelativePic0Designation` for $X\to\operatorname{Spec}A$ (a scheme `D.P`, a morphism `D.toBase` to $\operatorname{Spec}A$ and a zero section), with `hrep` asserting that $D$ represents the subfunctor of the relative Picard functor rigidified along $\varepsilon$ and cut out by the condition `algEquivZeroCut` (fibrewise algebraic equivalence to zero): there is a Poincaré rigidified line bundle over `D.toBase` satisfying the condition, every such bundle over a base $T$ is induced by a unique $T$-point of `D.toBase` up to isomorphism, and the pullback along the zero section is trivial. Further `hsm`, `hsep`: `D.toBase` is smooth and separated. The hypothesis `hreps` asserts the analogous representability of the base change `D.baseChange k` for $X_k$ with the base-changed section, and `hPk` provides an isomorphism between its Poincaré bundle and the base change of that of $D$. Similarly $D_1$, $D_2$ with `hrep₁`, `hrep₂` represent the corresponding functors for $c_1$, $c_2$ rigidified along $\varepsilon_1$, $\varepsilon_2$.
--
--   Let $\nu_2$ be a morphism from `(D.baseChange k).toBase` to `D₂.toBase` over $k$, characterised by `hν₂`: for every $k$-scheme $T$ and every $T$-point $a$ of `(D.baseChange k).toBase`, the pullback of the Poincaré bundle of $D_2$ along $a$ followed by $\nu_2$ is isomorphic to the rigidification (in the sense of `Scheme.Modules.rigidify` along the rigidifying section of $\varepsilon_2$) of the pullback along `curveChange i₂.1 i₂.2 t` of the pullback of the Poincaré bundle of `D.baseChange k` along $a$; thus $\nu_2$ is the restriction-to-$C_2$ homomorphism. The restriction to $C_1$ is `RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some`, the morphism classifying, via the universal property of $D_1$, the pullback of the Poincaré bundle of `D.baseChange k` along $i_1$.
--
--   **Generic fibre over $L$ and over $\overline{\mathbb{Q}}$.** With $A$- and $L$-algebra structures on $\mathrm{AlgebraicClosure}\,\mathbb{Q}$ forming a tower, the hypotheses `hsmL`, `hgiL` state that the base change of $X$ to $L$ is smooth of relative dimension $1$ and geometrically integral, and `hprL`, `hgcL` that `pullback.snd D.toBase (specMap A L)` is proper and geometrically connected. Let $M_\eta$ be a `CurveModel` over $\overline{\mathbb{Q}}$ of the function field [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) (a smooth proper integral curve with a fixed isomorphism of its function field with that field and a bijection between its closed points and the places), let $e_\eta$ be an isomorphism from $M_\eta.C$ to the geometric fibre $X_{\overline{\mathbb{Q}}}$ compatible with the structure morphisms (`heη`), with the preimage of the finite chart non-empty, and let `hMηpin` pin the reading of the model: for every element $a$ of the finite chart algebra, the germ of $a$ at the generic point, transported through $M_\eta.\mathrm{ffEquiv}$, has Laurent expansion the coefficientwise image under $L\to\overline{\mathbb{Q}}$ of the expansion of $a$. The hypothesis `hgal` asserts Galois equivariance of the point-to-place bijection: for every $g\in\operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ fixing the image of $L$ pointwise and all $\overline{\mathbb{Q}}$-points $x,x'$ of $M_\eta.C$ such that $x'$ composed into the finite chart equals $\operatorname{Spec}(g)$ followed by $x$ composed into the finite chart, one has $M_\eta.\mathrm{pointEquivPlace}\,x' = \mathrm{arithmeticGalois}\,g\cdot M_\eta.\mathrm{pointEquivPlace}\,x$.
--
--   The hypothesis `hin` is [`ModularCurve.HeckeDiamondInputsAll (M * p)`](def/ModularCurve_X1HeckeModule.html#L58): for every prime $\ell$ the predicate `HeckeInputsOneAlong` holds over $\overline{\mathbb{Q}}$ at level $Mp$, and for every $d$ coprime to $Mp$ there exist a diamond automorphism of `x1FunctionField (M * p)` satisfying `IsDiamondAut` and an automorphism of `x1FunctionFieldBar (M * p)` over $\overline{\mathbb{Q}}$ which is its base change. The hypothesis `hcomm` is [`ModularCurve.HeckeDiamondCommuteBar (M * p)`](def/ModularCurve_X1HeckeModule.html#L54): the operators `heckeDiamondGenBar` attached to the generators commute pairwise.
--
--   **Galois action on $A$.** A multiplicative semiring action of $\operatorname{Gal}(L/\mathbb{Q})$ on $A$ is fixed, compatible with $A\to L$ (`hΓA`).
--
--   **Group-theoretic frame for the special fibre.** Let $G$ be a [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9): abelian groups `G.J0s`, `G.JI`, `G.JE`, a subgroup `G.torus` of `G.J0s`, and a surjective homomorphism `G.proj : G.J0s →+ G.JI × G.JE` with kernel `G.torus`. Bijections `pts`, `ptsI`, `ptsE` identify `G.J0s`, `G.JI`, `G.JE` with the $k$-points of `(D.baseChange k).toBase`, `D₁.toBase`, `D₂.toBase` respectively; `hadd`, `haddI`, `haddE` state that under each of these bijections the Poincaré pullback along a sum is isomorphic to the tensor product of the pullbacks; and `hproj` states that for every $x\in G.J0s$ the first component of `G.proj x` corresponds to $\mathrm{pts}(x)$ followed by the restriction morphism to $D_1$, and the second component to $\mathrm{pts}(x)$ followed by $\nu_2$.
--
--   **Hecke, diamond and Galois operators on $D$.** A bijection `gpts` identifies [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186), the degree-zero divisor class group of `x1FunctionFieldBar (M * p)`, with the $\overline{\mathbb{Q}}$-points of `D.toBase`. For each $t$ in [`ModularCurve.HeckeAlgOne`](def/ModularCurve_X1HeckeModule.html#L16) $=\mathbb{Z}[X_i : i\in \mathrm{Primes}\sqcup\mathbb{N}]$ an endomorphism $\varphi(t)$ of `D.toBase` over $\operatorname{Spec}A$ is given, and for each $s\in\operatorname{Gal}(L/\mathbb{Q})$ a morphism $\tau(s) : D.P\to D.P$ lying over $\operatorname{Spec}$ of the ring homomorphism $a\mapsto s\cdot a$ of $A$. The hypotheses are: `hφmul`, each $\varphi(t)$ is additive for the relative group law carried by `hrep.some` through `algEquivZeroGroupCut`; `hφpts`, for the module structure [`ModularCurve.heckeModuleOneBar (M * p)`](def/ModularCurve_X1HeckeModule.html#L129) one has $\mathrm{gpts}(t\cdot x) = \mathrm{gpts}(x)$ followed by $\varphi(t)$; `hτ1`, $\tau(1)$ is the identity of `D.P`; `hτmul`, $\tau(ss')$ is $\tau(s)$ followed by $\tau(s')$; `hτφ`, $\tau(s)$ and $\varphi(t)$ commute; `hgadd`, `gpts` is additive for the relative group law; and `hτpts`, for $\sigma'\in\operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ inducing $s$ on $L$ and every $x$, $\mathrm{gpts}(\sigma'\cdot x)$ equals $\operatorname{Spec}(\sigma')$ followed by $\mathrm{gpts}(x)$ followed by $\tau(s^{-1})$.
--
--   **Abel–Jacobi data.** The hypothesis `hDL` gives representability over $L$ by `D.baseChange L`; `ajL` is a morphism from $X_L$ to `(D.baseChange L).toBase` over $L$, `kL` a morphism $X_{\overline{\mathbb{Q}}}\to X_L$, `ajbar` a morphism $M_\eta.C\to D.P$ and $\bar\varepsilon$ a $\overline{\mathbb{Q}}$-point of $M_\eta.C$. Here `hPL` compares the Poincaré bundle over $L$ with the base change of that of $D$; `hajLε` says the section of $X_L$ induced by $\varepsilon$ followed by `ajL` is the zero section; `hajL` is the Abel–Jacobi property: for every field $K'$, every $K'$-point $t$ of $\operatorname{Spec}L$ and every $x$ of $X_L$ over $t$, the pullback of the Poincaré bundle along $x$ followed by `ajL` is isomorphic to the line bundle of the relative effective Cartier divisor of the point $x$ tensored with the ideal module of the divisor of the cusp section; `hkL₁`, `hkL₂` fix `kL` on the two projections; `hajbar` defines `ajbar` as $e_\eta$ followed by `kL`, `ajL` and the first projection; `hajbar_over` places it over the base; `hεbar` says $\bar\varepsilon$ maps to the cusp $\varepsilon$ and `hεbar_aj` that $\bar\varepsilon$ followed by `ajbar` is the zero section; and `hpts_aj` says that for all $\overline{\mathbb{Q}}$-points $x$ and $s$ of $M_\eta.C$ with $s$ the cusp there is a degree-zero divisor $D_v$ equal to $[\,$place of $x\,]-[\,$place of $s\,]$ whose class satisfies $\mathrm{gpts}(\mathrm{Pic}^0\text{-class of } D_v) = x$ followed by `ajbar`.
--
--   **Gauss reading on $C_1$, and the cusp.** Let $w$ be an [`ModularCurve.IntegralWeightOneForm k M`](def/ModularCurve_IgusaFunctionFieldX1.html#L16) (a weight-one modular form on $\Gamma_1(M)$ with integral $q$-expansion whose reduction into $k$ is non-zero), let $\mathrm{Mdl}_1$ be a curve model over $k$ of the Igusa function field [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35), and let $e_1 : \mathrm{Mdl}_1.C\cong C_1$ be an isomorphism over $k$ (`he₁`), with the preimage of the finite chart non-empty. The hypothesis `hgauss₁` is the Gauss reading: for every $a$ in the finite chart algebra and all power series $x,y$ over $A$ with the reduction of $y$ to $k$ non-zero and $a\cdot \hat y = \hat x$ in Laurent series over $L$, the germ of $a$ at the generic point of $C_1$, read through $\mathrm{Mdl}_1$ and the Igusa function field, has Laurent expansion $\bar x/\bar y$ over $k$. Finally `hεC₂` states that no point in the image of the base-changed cusp section lies in the image of $i_2$, and `hεgal` states the Galois stability of the cusp: for every $s\in\operatorname{Gal}(L/\mathbb{Q})$, every endomorphism $w_s$ of the two-chart model lying over $\operatorname{Spec}$ of the action of $s$ on $A$, and every ring automorphism $\rho_s$ of the finite chart algebra acting on Laurent coefficients through $s$ and compatible with $w_s$ via the finite chart, one has $\varepsilon$ followed by $w_s$ equal to $\operatorname{Spec}$ of the action of $s$ followed by $\varepsilon$.
--
--   **Conclusion.** Two assertions hold.
--
--   First, for every $s\in\operatorname{Gal}(L/\mathbb{Q})$ and all $k$-points $v,v'$ of `(D.baseChange k).toBase` such that $v'$ followed by `pullback.fst D.toBase (specMap A k)` equals $v$ followed by that projection and then by $\tau(s)$, the images of $v'$ and of $v$ under the restriction morphism `RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some` to $D_1$ coincide.
--
--   Second, for every unit $b$ of $\mathbb{Z}/p$ and every $s\in\operatorname{Gal}(L/\mathbb{Q})$ with $s\zeta = \zeta^{\,b}$ (the exponent being the canonical representative of $b$), for every natural number $d$ coprime to $Mp$ with $d\equiv 1 \pmod M$ and $d\equiv b\pmod p$, and for all $k$-points $v, v'''$ of `(D.baseChange k).toBase` such that $v'''$ followed by `pullback.fst D.toBase (specMap A k)` equals $v$ followed by that projection, then by $\varphi(\langle d\rangle)$ where $\langle d\rangle$ is [`ModularCurve.diamondGen d`](def/ModularCurve_X1HeckeModule.html#L20), and then by $\tau(s^{-1})$, the images of $v'''$ and of $v$ under $\nu_2$ coincide.
--
--   This is the comparison, on the special fibre at $p$ of the Picard scheme of the model of $X_1(Mp)$, between the action of $\operatorname{Gal}(\mathbb{Q}(\zeta_p)/\mathbb{Q})$ and the diamond operators: on the Igusa component $C_1$ carrying the cusp section, the component on which $A$-integral $q$-expansions are read by the Gauss reading, the Galois operators $\tau_s$ act trivially after restriction, while on the other component $C_2$ the restriction of $v\cdot\langle d\rangle\cdot\tau_{s^{-1}}$ agrees with that of $v$ whenever $d\equiv b \pmod p$ and $s\zeta_p=\zeta_p^{\,b}$. It is used in assembling the operations on the Néron special fibre at $p$ and in the identification of the two projections of the component group datum, the input to the level-lowering step at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_postComp_pullbackHom_galois_eq_and_postComp_diamond_comp_galoisInv_eq_of_gaussReading_specialFibre_twoChartModel_x1_mul_of_abelJacobi.lean

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
import Definitions.Def_ModularCurve_JOnePOps
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_HopfAlgebra_FVectStructure
import Definitions.Def_HopfAlgebra_RaynaudNormalFormDatum
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
open scoped TensorProduct

theorem ModularCurve.XOneP.postComp_pullbackHom_galois_eq_and_postComp_diamond_comp_galoisInv_eq_of_gaussReading_specialFibre_twoChartModel_x1_mul_of_abelJacobi
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
      ε.1 ≫ ws = Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)) ≫ ε.1) :

    (
      ∀ (s : L ≃ₐ[ℚ] L) (v v' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase),
        v'.1 ≫ pullback.fst D.toBase (specMap A k) = (v.1 ≫ pullback.fst D.toBase (specMap A k)) ≫ (τ s).1 →
          postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) v' = postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) v) ∧
    (
      ∀ (b : (ZMod p)ˣ) (s : L ≃ₐ[ℚ] L), s ζ = ζ ^ (b : ZMod p).val →
      ∀ d : ℕ, d.Coprime (M * p) → (d : ZMod M) = 1 → (d : ZMod p) = (b : ZMod p) →
      ∀ (v v''' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase),
        v'''.1 ≫ pullback.fst D.toBase (specMap A k) =
          (((v.1 ≫ pullback.fst D.toBase (specMap A k)) ≫ (φ (ModularCurve.diamondGen d)).1) ≫ (τ s⁻¹).1) →
          postComp ν₂ v''' = postComp ν₂ v) := by sorry
