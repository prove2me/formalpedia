-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_pDivisibleGroup_normFreePart_points_tateModule_valuation_lt_one_of_reduction_eq_zeroSection_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_pDivisibleGroup_normFreePart_points_tateModule_valuation_lt_one_of_reduction_eq_zeroSection_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/57a3b8b6-b5bd-5f1a-bfcd-f24fc7a553f1
-- title:
--   A p-divisible group over A for the norm-free part of J₁(Mp)
-- statement:
--   Arithmetic frame. Fix a prime $p$, a natural number $M$ with $5 \le M$ and $p \nmid M$, a field $L$ of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, and a primitive $p$-th root of unity $\zeta \in L$. Let $K$ be an intermediate field of $\mathrm{LaurentSeries}\ L$ over $L$, assumed by `hK` to be [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the field generated over $L$ by the coefficientwise image of the $q$-expansion function field of $\Gamma_1(Mp)$. Let $A$ be a discrete valuation domain with fraction field $L$, with $p$ in its maximal ideal (`hAp`) and with $\zeta$ in the image of $A$ (`hζA`), an $A$-algebra structure on $K$ compatible with the tower $A \to L \to K$, and a nonzero $j \in K$ whose Laurent expansion is [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81) (`hj`). All that follows concerns the two-chart model [`ModularCurve.TwoChart.modelTo A ↥K j`](def/ModularCurve_TwoChartModel.html#L252) over $\operatorname{Spec} A$, glued from the spectra of the integral closures of $A[j]$ and $A[j^{-1}]$ in $K$; it is assumed proper.
--
--   Special fibre. An algebraically closed field $k$ of characteristic $p$ which is an $A$-algebra; two proper smooth geometrically integral curves $c_1 : C_1 \to \operatorname{Spec} k$ and $c_2 : C_2 \to \operatorname{Spec} k$ of relative dimension $1$, together with closed immersions $i_1, i_2$ of them over $k$ into the base change of the two-chart model to $k$; the hypothesis `hcover` that every point of that base change lies in the image of $i_1$ or of $i_2$; `hred`, that the fibre product of $i_1$ and $i_2$ is reduced; and a positive natural number $n$ equal to its cardinality (`hn`, `hn0`).
--
--   Sections. A section $\varepsilon$ of the two-chart model over $\operatorname{Spec} A$, sections $\varepsilon_1, \varepsilon_2$ of $c_1, c_2$, and `hε₁`, that $\varepsilon_1$ followed by $i_1$ is the base change of $\varepsilon$ to $k$.
--
--   Relative $\mathrm{Pic}^0$ data. A designation $D$ for the two-chart model over $A$, that is a scheme `D.P` with a structure morphism `D.toBase` to $\operatorname{Spec} A$ and a zero section; `hrep`, the (nonempty) datum that $D$ represents the subfunctor of rigidified line bundles satisfying `algEquivZeroCut`, i.e. those whose fibres over algebraically closed points are algebraically equivalent to zero, by a Poincaré bundle with the usual universal property and triviality along the zero section; and `hsm`, `hsep`, that `D.toBase` is smooth and separated. Over $k$: `hreps`, the analogous representability for the base change of the curve and of $D$; `hPk`, an isomorphism between the Poincaré bundle over $k$ and the base change of the one over $A$; designations $D_1, D_2$ for $c_1, c_2$ with representability data `hrep₁`, `hrep₂`; and a morphism $\nu_2$ from $(D \otimes_A k).\mathrm{toBase}$ to $D_2.\mathrm{toBase}$ over $k$ which, by `hν₂`, induces pullback of line bundles along $i_2$: for every $k$-scheme $t$ and section $a$ of $(D \otimes_A k).\mathrm{toBase}$ over $t$, the Poincaré bundle of $D_2$ pulled back along $a$ followed by $\nu_2$ is isomorphic to the rigidification of the pullback along `curveChange i₂` of the Poincaré bundle pulled back along $a$.
--
--   Generic fibre and the curve model over $\overline{\mathbb{Q}}$. Algebra structures making $A \to L \to \mathrm{AlgebraicClosure}\ \mathbb{Q}$ a tower; `hsmL`, `hgiL`, that the base change of the two-chart model to $L$ is smooth of relative dimension $1$ and geometrically integral; `hprL`, `hgcL`, that the base change of `D.toBase` to $L$ is proper and geometrically connected. Further, a curve model $M_\eta$ over $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ with function field [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) — a proper smooth integral scheme with a ring isomorphism of that field with its function field and a bijection between its closed points and the places of the field — an isomorphism $e_\eta$ of $M_\eta.C$ with the base change of the two-chart model to $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ compatible with the structure morphisms (`heη`), the nonemptiness of the finite-chart open of $M_\eta.C$ obtained as the preimage of the image of [`ModularCurve.TwoChart.ιFin`](def/ModularCurve_TwoChartModel.html#L231), and the pinning `hMηpin`: each element of the finite chart algebra, read through $e_\eta$ into the function field of $M_\eta.C$ and transported by $M_\eta.\mathrm{ffEquiv}^{-1}$, has Laurent expansion the coefficientwise image under $L \to \mathrm{AlgebraicClosure}\ \mathbb{Q}$ of its expansion in $K$. The hypothesis `hgal` states that for every automorphism $g$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ over $\mathbb{Q}$ fixing $L$ pointwise and every pair of geometric points $x, x'$ of $M_\eta.C$ with $x'$ (read into the chart) equal to $\operatorname{Spec} g$ followed by $x$, the place attached to $x'$ is the [`ModularCurve.arithmeticGalois`](def/ModularCurve_ArithmeticGalois.html#L54) image of $g$ applied to the place attached to $x$.
--
--   Hecke inputs. The hypotheses `hin` ([`ModularCurve.HeckeDiamondInputsAll (M * p)`](def/ModularCurve_X1HeckeModule.html#L58): the Hecke input packages at all primes, and for each $d$ coprime to $Mp$ the existence of a diamond automorphism of the function field and of a base-changed one) and `hcomm` ([`ModularCurve.HeckeDiamondCommuteBar (M * p)`](def/ModularCurve_X1HeckeModule.html#L54): the Hecke and diamond generators commute on $J_1(Mp)$). A multiplicative semiring action of $\mathrm{Gal}(L/\mathbb{Q})$ on $A$ compatible with $A \to L$ (`hΓA`).
--
--   Special-fibre group dictionary. A datum $G$ of type [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9), consisting of abelian groups `G.J0s`, `G.JI`, `G.JE`, a subgroup `G.torus` of `G.J0s`, and a surjective homomorphism `G.proj : G.J0s →+ G.JI × G.JE` with kernel `G.torus`; bijections `pts`, `ptsI`, `ptsE` of these three groups with the $k$-sections of $(D \otimes_A k).\mathrm{toBase}$, $D_1.\mathrm{toBase}$, $D_2.\mathrm{toBase}$; the additivity hypotheses `hadd`, `haddI`, `haddE`, each saying that the Poincaré pullback along the section of a sum is isomorphic to the tensor product of the Poincaré pullbacks; and `hproj`, that `ptsI` of the first component of `G.proj x` is `pts x` followed by the pullback morphism induced by $i_1$, and `ptsE` of the second component is `pts x` followed by $\nu_2$.
--
--   Generic points, Hecke and Galois operators on $D$. A bijection `gpts` between $J_1(Mp) = \mathrm{Pic}^0$ of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) and the sections of `D.toBase` over $\operatorname{Spec} \mathrm{AlgebraicClosure}\ \mathbb{Q} \to \operatorname{Spec} A$; a map $\varphi$ from [`ModularCurve.HeckeAlgOne`](def/ModularCurve_X1HeckeModule.html#L16) to endomorphisms of `D.toBase` over $A$; and for each $s \in \mathrm{Gal}(L/\mathbb{Q})$ a morphism $\tau(s)$ of `D.P` semilinear over the induced automorphism of $A$. These satisfy: `hφmul`, each $\varphi(t)$ is additive for the relative group law supplied by `hrep`; `hφpts`, `gpts` intertwines the Hecke action [`ModularCurve.heckeModuleOneBar (M * p)`](def/ModularCurve_X1HeckeModule.html#L129) with post-composition by $\varphi(t)$; `hτ1`, `hτmul`, that $\tau$ is multiplicative with $\tau(1)$ the identity of `D.P`; `hτφ`, that each $\tau(s)$ commutes with each $\varphi(t)$; `hgadd`, that `gpts` is additive for the relative group law; and `hτpts`, that for $\sigma'$ a $\mathbb{Q}$-automorphism of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ restricting to $s$ on $L$, `gpts (σ' • x)` equals $\operatorname{Spec} \sigma'$ followed by `gpts x` followed by $\tau(s^{-1})$.
--
--   Abel–Jacobi data. The representability datum `hDL` over $L$; a section `ajL` of $(D \otimes_A L).\mathrm{toBase}$ over the base-changed curve; a morphism `kL` between the base changes of the two-chart model to $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ and to $L$ compatible with both projections (`hkL₁`, `hkL₂`); a morphism `ajbar` from $M_\eta.C$ to `D.P` and a geometric point `εbar` of $M_\eta.C$. The hypotheses are: `hPL`, comparison of the Poincaré bundle over $L$ with the base change of the one over $A$; `hajLε`, that the base-changed section $\varepsilon$ followed by `ajL` is the zero section; `hajL`, that for every field $K'$, every $K'$-point $t$ of $\operatorname{Spec} L$ and every section $x$ over $t$ of the base-changed curve, the Poincaré bundle pulled back along $x$ followed by `ajL` is isomorphic to the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of the divisor of $\varepsilon$, i.e. `ajL` is the Abel–Jacobi map $x \mapsto [x] - [\varepsilon]$; `hajbar`, that `ajbar` is $e_\eta$ followed by `kL`, `ajL` and the first projection; `hajbar_over`, its compatibility with the structure morphisms; `hεbar` and `hεbar_aj`, that `εbar` lies over $\varepsilon$ and is sent by `ajbar` to the zero section; and `hpts_aj`, that for geometric points $x, s$ of $M_\eta.C$ with $s$ lying over $\varepsilon$ there is a degree-zero divisor $Dv$ on [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) equal to $[\,\mathrm{place}(x)\,] - [\,\mathrm{place}(s)\,]$ with `gpts` of its class equal to $x$ followed by `ajbar`.
--
--   The norm-free abelian subscheme. A scheme $\mathcal{A}$ with a morphism $a$ to $\operatorname{Spec} A$ and a closed immersion $\iota$ of $\mathcal{A}$ into `D.P` over $A$ (`h𝒜cl`), with: `h𝒜pr`, `h𝒜sm`, $a$ proper and smooth; `h𝒜conn`, all geometric fibres of $a$ connected; `h𝒜grp`, that the unit, the multiplication and the inverse of the relative group law on `D.toBase` factor through $\iota$ on sections of $a$; `h𝒜gen`, that a point $x$ of $J_1(Mp)$ lies in [`ModularCurve.normFreePartAt (M * p) p`](def/ModularCurve_X1PrimitiveSpecializationAtP.html#L29) — the image of the endomorphism $y \mapsto |S| y - \sum_{d \in S} \langle d \rangle y$, where $S$ is the set of $d < Mp$ coprime to $Mp$ with $d \equiv 1 \bmod M$ — if and only if the section `gpts x` over $\operatorname{Spec} \mathrm{AlgebraicClosure}\ \mathbb{Q}$ factors through $\iota$; and `h𝒜hecke`, that each $\varphi(t)$ preserves $\mathcal{A}$ in the same sense.
--
--   Reduction data. A valuation subring $\mathrm{Pl}$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ with $p$ a non-unit of $\mathrm{Pl}$ (`hPl`), a ring homomorphism $\rho : A \to \mathrm{Pl}$ lifting $A \to \mathrm{AlgebraicClosure}\ \mathbb{Q}$ (`hρ`), and a homomorphism $\pi_k : \mathrm{Pl} \to k$ with $\pi_k \circ \rho$ the structure map $A \to k$ (`hAlgk`) and kernel the maximal ideal of $\mathrm{Pl}$ (`hπk`).
--
--   Conclusion. There exist a natural number $h$ (no value is specified), a $p$-divisible group $\mathcal{G}$ over $A$ of height parameter $h$ — levels $\mathcal{G}.\mathrm{level}\ v$ finite free Hopf algebras over $A$ of rank $p^{vh}$ with surjective transition maps whose kernels are the $p^v$-torsion ideals — a homomorphism $\Delta$ from $\mathcal{G}.\mathrm{Points}(\mathrm{AlgebraicClosure}\ \mathbb{Q})$ (the direct limit of the convolution groups of algebra homomorphisms of the levels) to $J_1(Mp)$, and a $\mathbb{Z}_p$-linear map $e$ from $T_p\,\mathcal{G}.\mathrm{Points}(\mathrm{AlgebraicClosure}\ \mathbb{Q})$ to $T_p J_1(Mp)$, where $T_p N$ denotes the group of sequences $(x_n)$ in $N$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$, such that:
--
--   (i) $\Delta$ is injective;
--
--   (ii) for every $v$ and every $y \in J_1(Mp)$: $p^v y = 0$ and $y$ lies in [`ModularCurve.normFreePartAt (M * p) p`](def/ModularCurve_X1PrimitiveSpecializationAtP.html#L29) if and only if $y = \Delta(x)$ for some level-$v$ point $x$ of $\mathcal{G}$ over $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, taken through `pointsMkAdd`;
--
--   (iii) $e$ is computed componentwise by $\Delta$: the $n$-th term of $e(x)$ is $\Delta$ of the $n$-th term of $x$;
--
--   (iv) $e$ is injective;
--
--   (v) an element $y$ of $T_p J_1(Mp)$ lies in the range of $e$ if and only if every term of $y$ lies in [`ModularCurve.normFreePartAt (M * p) p`](def/ModularCurve_X1PrimitiveSpecializationAtP.html#L29);
--
--   (vi) $e$ is equivariant for the Galois actions in the following sense: for every automorphism $\tau$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ over $\mathbb{Q}$ and every $A$-algebra automorphism $\tau'$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ agreeing with $\tau$ pointwise, $e$ composed with the action of $\tau'$ on $T_p\,\mathcal{G}.\mathrm{Points}$ equals the action of $\tau$ on $T_p J_1(Mp)$ composed with $e$;
--
--   (vii) reduction clause: for every $v$, every level-$v$ point $g$ of $\mathcal{G}$ over $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ and every section $z$ of `D.toBase` over $\operatorname{Spec} \rho$, if the section `gpts` of $\Delta$ of the class of $g$ equals $\operatorname{Spec}$ of the inclusion $\mathrm{Pl} \hookrightarrow \mathrm{AlgebraicClosure}\ \mathbb{Q}$ followed by $z$, and if $\operatorname{Spec} \pi_k$ followed by $z$ is the structure morphism $\operatorname{Spec} k \to \operatorname{Spec} A$ followed by the zero section of $D$, then for every $a$ in $\mathcal{G}.\mathrm{level}\ v$ the valuation attached to $\mathrm{Pl}$ of $g(a) - \varepsilon_{\mathcal{G}}(a)$ is $< 1$, where $g(a)$ is the value of the algebra homomorphism underlying $g$ and $\varepsilon_{\mathcal{G}}(a)$ is the image in $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ of the counit of $a$.
--
--   This packages the $p$-divisible group of the norm-free abelian subscheme $\mathcal{A} \subset \mathrm{Pic}^0$ of the two-chart model of $X_1(Mp)$ over the discrete valuation ring $A =$ the ring of integers data of $\mathbb{Q}(\zeta_p)$ localised at $p$: a dictionary $\Delta$ between its $\overline{\mathbb{Q}}$-points and the $p$-power torsion of the norm-free part of $J_1(Mp)$, the induced map $e$ of Tate modules with its range and its equivariance for $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}(\zeta_p))$, and a valuation-theoretic reading of reduction to the zero section. It is used by the statements about the norm-free family that compute the pairing and the vanishing of Tate-module classes for $J_1(Mp)$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_pDivisibleGroup_normFreePart_points_tateModule_valuation_lt_one_of_reduction_eq_zeroSection_twoChartModel_x1_mul.lean

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
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.exists_pDivisibleGroup_normFreePart_points_tateModule_valuation_lt_one_of_reduction_eq_zeroSection_twoChartModel_x1_mul
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
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ) (hπk : RingHom.ker πk = IsLocalRing.maximalIdeal ↥Pl) :
    ∃ (h : ℕ) (𝒢 : PDivisibleGroup A p h)
      (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JOne (M * p))
      (e : TateModule p (𝒢.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JOne (M * p))),

      Function.Injective Δ ∧

      (∀ (v : ℕ) (y : ModularCurve.JOne (M * p)),
        ((p ^ v) • y = 0 ∧ y ∈ ModularCurve.normFreePartAt (M * p) p) ↔
        ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y) ∧

      (∀ (x : TateModule p (𝒢.Points (AlgebraicClosure ℚ))) (n : ℕ),
        ((e x : TateModule p (ModularCurve.JOne (M * p))) : ℕ → ModularCurve.JOne (M * p)) n =
          Δ ((x : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) n)) ∧
      Function.Injective e ∧
      (∀ y : TateModule p (ModularCurve.JOne (M * p)), y ∈ LinearMap.range e ↔
        ∀ n : ℕ, (y : ℕ → ModularCurve.JOne (M * p)) n ∈ ModularCurve.normFreePartAt (M * p) p) ∧
      (∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[A] AlgebraicClosure ℚ),
        (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
        ∀ x : TateModule p (𝒢.Points (AlgebraicClosure ℚ)),
          e (𝒢.tateModuleRep (AlgebraicClosure ℚ) τ' x) =
            TateModule.rep p (ModularCurve.JOne (M * p)) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) τ (e x)) ∧

      (∀ (v : ℕ) (g : 𝒢.Point (AlgebraicClosure ℚ) v) (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase),
        (gpts (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul g)))).1 =
          Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z.1 →
        Spec.map (CommRingCat.ofHom πk) ≫ z.1 = specMap A k ≫ D.zeroSection →
        ∀ a : 𝒢.level v,
          Pl.valuation (PDivisibleGroup.Point.toAlgHom g a - algebraMap A (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) := by sorry
