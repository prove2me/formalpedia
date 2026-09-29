-- Prove2me | Theorems.Thm_ModularCurve_XOneP_proj_snd_eq_zero_of_points_eq_reduction_of_surjective_residue_of_forall_mem_support_exists_section_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.proj_snd_eq_zero_of_points_eq_reduction_of_surjective_residue_of_forall_mem_support_exists_section_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/99f6eef7-b543-520d-a4e3-08cc42d09681
-- title:
--   Vanishing étale coordinate for classes reducing off the crossings
-- statement:
--   Throughout, $p$ is a prime, $M \ge 5$ is a natural number not divisible by $p$, $L$ is a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, $\zeta \in L$ is a primitive $p$-th root of unity, and $K$ is the intermediate field of $\mathrm{LaurentSeries}\,L$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), the base change to $L$ of the function field of $X_1(Mp)$. Further, $A$ is a discrete valuation domain with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A$, $K$ is an $A$-algebra compatibly with $A \to L \to K$, and $j \in K$ is the element whose image in $\mathrm{LaurentSeries}\,L$ is the coefficientwise image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), with $j \neq 0$. The relevant arithmetic surface is the two-chart model with structure morphism $X :=$ [`ModularCurve.TwoChart.modelTo A ↥K j`](def/ModularCurve_TwoChartModel.html#L252) over $\operatorname{Spec} A$, assumed proper.
--
--   *Special fibre.* $k$ is an algebraically closed field of characteristic $p$ and an $A$-algebra; $c_1 : C_1 \to \operatorname{Spec} k$ and $c_2 : C_2 \to \operatorname{Spec} k$ are proper, smooth of relative dimension $1$ and geometrically integral; $i_1, i_2$ are closed immersions of $C_1$, $C_2$ over $k$ into the base change of $X$ along $A \to k$. The hypothesis `hcover` states that every point of $X \times_{\operatorname{Spec} A} \operatorname{Spec} k$ lies in the image of $i_1$ or of $i_2$; `hred` states that $\mathrm{pullback}\ i_1\ i_2$ (the scheme-theoretic intersection $C_1 \cap C_2$) is reduced, and `hn`, `hn0` fix $n = \mathrm{Nat.card}$ of that intersection with $0 < n$.
--
--   *Sections and relative $\mathrm{Pic}^0$ data.* $\varepsilon$ is a section of $X$ over $\operatorname{Spec} A$, and $\varepsilon_1$, $\varepsilon_2$ are $k$-sections of $c_1$, $c_2$, with `hε₁` asserting that $\varepsilon_1$ followed by $i_1$ is the base-changed section of $\varepsilon$. $D$ is a `RelativePic0Designation` for $X$, i.e. a scheme $D.P$ with structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec} A$ and a zero section; `hrep` asserts (non-emptily) that $D$ represents the relative sub-Picard functor of $X$ rigidified along $\varepsilon$ for the cut `algEquivZeroCut` (the fibrewise algebraically-trivial condition), carrying a Poincaré rigidified line bundle with the universal property and triviality at the zero section. The hypotheses `hsm`, `hsep` require $D.\mathrm{toBase}$ to be smooth and separated.
--
--   *Base changes and comparison of Poincaré bundles.* `hreps` asserts that $D.\mathrm{baseChange}\ k$ represents the corresponding functor for the base change of $X$ to $k$ with section $\mathrm{sectionBaseChange}\ k\ \varepsilon$, and `hPk` that its Poincaré bundle is isomorphic to the base change (via `BaseChange.ofR`) of the pullback of the Poincaré bundle of `hrep` along $\mathrm{pullback.fst}\ D.\mathrm{toBase}\ (\mathrm{specMap}\ A\ k)$. Similarly $D_1$, $D_2$ with `hrep₁`, `hrep₂` are designations representing these functors for $c_1, \varepsilon_1$ and $c_2, \varepsilon_2$ over $k$. The morphism $\nu_2$ from $(D.\mathrm{baseChange}\ k).\mathrm{toBase}$ to $D_2.\mathrm{toBase}$ over $k$ is required by `hν₂` to be the restriction-to-$C_2$ map: for every $k$-scheme $t : T \to \operatorname{Spec} k$ and every section $a$ of $(D.\mathrm{baseChange}\ k).\mathrm{toBase}$ over $t$, the pullback of the Poincaré bundle of `hrep₂` along $a$ followed by $\nu_2$ is isomorphic to the `rigidify` along the rigidifying section of $c_2$ of the pullback, along `curveChange i₁`-style morphism `curveChange i₂.1 i₂.2 t`, of the pullback of the Poincaré bundle of `hreps` along $a$.
--
--   *Geometric generic fibre.* With $A$, $L$ mapping compatibly to $\overline{\mathbb{Q}} = \mathrm{AlgebraicClosure}\ \mathbb{Q}$, $M\eta$ is a `CurveModel` over $\overline{\mathbb{Q}}$ of the function field [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182), and $e\eta$ is an isomorphism from $M\eta.C$ to $X \times_{\operatorname{Spec} A} \operatorname{Spec} \overline{\mathbb{Q}}$ compatible with the structure morphisms (`heη`).
--
--   *Néron special fibre group data.* $G$ is a [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9): abelian groups $G.J0s$, $G.JI$, $G.JE$, a subgroup $G.\mathrm{torus} \le G.J0s$, and a surjective homomorphism $G.\mathrm{proj} : G.J0s \to G.JI \times G.JE$ with kernel $G.\mathrm{torus}$. The bijections $\mathrm{pts}$, $\mathrm{ptsI}$, $\mathrm{ptsE}$ identify $G.J0s$, $G.JI$, $G.JE$ with the $k$-sections of $(D.\mathrm{baseChange}\ k).\mathrm{toBase}$, $D_1.\mathrm{toBase}$, $D_2.\mathrm{toBase}$ respectively; `hadd`, `haddI`, `haddE` state that each is additive in the sense that the Poincaré pullback at a sum is isomorphic to the tensor product of the Poincaré pullbacks; and `hproj` states, for every $x \in G.J0s$, that $\mathrm{ptsI}$ of the first component of $G.\mathrm{proj}\ x$ is the composite of $\mathrm{pts}\ x$ with `RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some`, and that $\mathrm{ptsE}$ of the second component is the composite of $\mathrm{pts}\ x$ with $\nu_2$.
--
--   *Abel–Jacobi data.* $\mathrm{gpts}$ is a bijection from [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186), the group $\mathrm{Pic}^0$ of the geometric generic function field, to the sections of $D.\mathrm{toBase}$ over $\mathrm{specMap}\ A\ \overline{\mathbb{Q}}$, additive for the relative group law of `hrep.some` (`hgadd`). Over $L$: `hDL` is the representability statement for $D.\mathrm{baseChange}\ L$, $\mathrm{ajL}$ is a morphism from the base change of $X$ to $L$ into $(D.\mathrm{baseChange}\ L).\mathrm{toBase}$ over that curve, $kL$ is a morphism between the fibres over $\overline{\mathbb{Q}}$ and over $L$, $\overline{\mathrm{aj}} : M\eta.C \to D.P$, and $\overline{\varepsilon}$ is an $\overline{\mathbb{Q}}$-point of $M\eta.C$. These are constrained by: `hPL` (the Poincaré bundle over $L$ is the base change of the one for `hrep`); `hajLε` ($\varepsilon$ base changed to $L$ followed by $\mathrm{ajL}$ is the zero section); `hajL` (for every field $K'$, every $t : \operatorname{Spec} K' \to \operatorname{Spec} L$ and every point $x$ of the $L$-curve over $t$, the pullback of the Poincaré bundle of `hDL` along $x$ followed by $\mathrm{ajL}$ is isomorphic to the line bundle of the relative effective Cartier divisor of the point $x$ tensored with the ideal module of the divisor of $t$ followed by the base-changed $\varepsilon$, i.e. $\mathrm{ajL}$ classifies $\mathcal{O}(x-\varepsilon)$); `hkL₁`, `hkL₂` (compatibility of $kL$ with the two projections, the second up to $\operatorname{Spec} \overline{\mathbb{Q}} \to \operatorname{Spec} L$); `hajbar` ($\overline{\mathrm{aj}} = e\eta$ followed by $kL$, $\mathrm{ajL}$ and $\mathrm{pullback.fst}\ D.\mathrm{toBase}\ (\mathrm{specMap}\ A\ L)$); `hajbar_over` (compatibility over the base); `hεbar` ($\overline{\varepsilon}$ is carried by $e\eta$ and the first projection to $\varepsilon$); `hεbar_aj` ($\overline{\varepsilon}$ followed by $\overline{\mathrm{aj}}$ is the zero section); and `hpts_aj`: for all $\overline{\mathbb{Q}}$-points $x, s$ of $M\eta.C$, if $s$ is carried to $\varepsilon$ as in `hεbar`, then there is a degree-zero divisor $D_v$ with $D_v = \delta_{P(x)} - \delta_{P(s)}$ for the places $P(\cdot) = M\eta.\mathrm{pointEquivPlace}(\cdot)$ and $\mathrm{gpts}(\mathrm{Pic0.mk}\ D_v) = x$ followed by $\overline{\mathrm{aj}}$.
--
--   *Igusa model of the cusp component and its coordinate.* $w$ is a [`ModularCurve.IntegralWeightOneForm k M`](def/ModularCurve_IgusaFunctionFieldX1.html#L16) (a weight-one form on $\Gamma_1(M)$ with an integral $q$-expansion whose reduction over $k$ is non-zero), $\mathrm{Mdl}_1$ is a curve model over $k$ of the Igusa function field [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35), and $e_1 : \mathrm{Mdl}_1.C \cong C_1$ is an isomorphism over $\operatorname{Spec} k$ (`he₁`). The isomorphism $\theta_1 : G.JI \cong \mathrm{Pic}^0$ of that Igusa function field is required by `hθpin₁` to be computed by divisors: for $g \in G.JI$ and a $k$-point $x$ of $c_1$, if the Poincaré pullback at $\mathrm{ptsI}\ g$ is isomorphic to the line bundle of the divisor of $x$ tensored with the ideal module of the divisor of $\varepsilon_1$, then there is a degree-zero divisor $D_v$ equal to the difference of the places of $x$ and of $\varepsilon_1$ (transported by $e_1^{-1}$) with $\theta_1 g = \mathrm{Pic0.mk}\ D_v$.
--
--   *Places and reduction.* $\mathrm{Pl}$ is a valuation subring of $\overline{\mathbb{Q}}$ with $p$ in its non-units (`hPl`), $\rho : A \to \mathrm{Pl}$ lifts the structure map (`hρ`), $O$ is a subring of $\overline{\mathbb{Q}}$ contained in $\mathrm{Pl}$ (`hO`) with a lift $\rho_O : A \to O$ of the structure map (`hρO`), and $\pi_k : \mathrm{Pl} \to k$ is a surjective ring homomorphism (`hπk`) with $A \to k$ equal to $\pi_k \circ \rho$ (`hAlgk`). Finally $\mathrm{red}_1$ is a map from places of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) over $\overline{\mathbb{Q}}$ to places of the Igusa function field over $k$, characterised by `hred₁`: for every place $P$, every section $\xi$ of $X$ over $\operatorname{Spec}$ of $\rho_O$ (an $O$-point of the two-chart model) and every $k$-point $c$ of $c_1$, if the generic point of $\xi$, restricted along $O \hookrightarrow \overline{\mathbb{Q}}$, is the point of the geometric generic fibre corresponding to $P$ via $M\eta.\mathrm{pointEquivPlace}^{-1}$ and $e\eta$, and if $c$ followed by $i_1$ and the first projection is the reduction of $\xi$ along $\pi_k \circ (O \hookrightarrow \mathrm{Pl})$, then $\mathrm{red}_1 P$ is the place of $\mathrm{Mdl}_1$ attached to $c$ transported by $e_1^{-1}$.
--
--   Under these hypotheses the assertion is the following. Let $D_v$ be a degree-zero divisor on the geometric generic fibre, an element of `Divisor.degZero` for $\overline{\mathbb{Q}}$ and [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182). Suppose that for every place $P$ in the support of $D_v$ there exist a section $\xi$ of $X$ over $\operatorname{Spec}$ of $\rho_O$ and a $k$-point $c$ of $c_1$ such that: (i) $\xi$ restricted along $O \hookrightarrow \overline{\mathbb{Q}}$ is the point of the geometric generic fibre corresponding to $P$ (composed with $e\eta$ and the first projection); (ii) $c$ followed by $i_1$ and the first projection equals $\xi$ reduced along $\pi_k \circ (O \hookrightarrow \mathrm{Pl})$; and (iii) for every point $t$ of the source of $c$, the image $c.\mathrm{base}\ t$ does not lie in the image of the base map of $\mathrm{pullback.fst}\ i_1\ i_2$, that is, $c$ avoids $C_1 \cap C_2$.
--
--   Then for every section $z$ of $D.\mathrm{toBase}$ over $\operatorname{Spec}$ of $\rho_O$ such that $\mathrm{gpts}(\mathrm{Pic0.mk}\ D_v)$ equals $z$ restricted along $O \hookrightarrow \overline{\mathbb{Q}}$, and for every $y \in G.J0s$ such that $\mathrm{pts}\ y$ followed by $\mathrm{pullback.fst}\ D.\mathrm{toBase}\ (\mathrm{specMap}\ A\ k)$ equals $z$ reduced along $\pi_k \circ (O \hookrightarrow \mathrm{Pl})$, one has
--   $$(G.\mathrm{proj}\ y).2 = 0,$$
--   i.e. the $G.JE$-component of $G.\mathrm{proj}\ y$ vanishes.
--
--   In the Raynaud-style description of the Néron special fibre of $J_1(Mp)$ at $p$, with the special fibre of the two-chart model of $X_1(Mp)$ covered by the two components $C_1$ (the Igusa, or cusp, component) and $C_2$, this statement computes one coordinate of the reduction map: a degree-zero class represented by a divisor whose support consists of $O$-integral points reducing into $C_1$ away from $C_1 \cap C_2$ reduces into the kernel of the $G.JE$-coordinate of $G.\mathrm{proj}$. It is the companion of the statement reading the $G.JI$-coordinate through $\theta_1$, and is used in the analysis of the reduction of the Hecke and diamond operators on the special fibre, in particular in the triangularity statements for $U_p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_proj_snd_eq_zero_of_points_eq_reduction_of_surjective_residue_of_forall_mem_support_exists_section_twoChartModel_x1_mul.lean

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

theorem ModularCurve.XOneP.proj_snd_eq_zero_of_points_eq_reduction_of_surjective_residue_of_forall_mem_support_exists_section_twoChartModel_x1_mul
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

    (θ₁ : G.JI ≃+ AlgebraicCurve.Pic0 k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hθpin₁ : ∀ (g : G.JI) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
      Nonempty ((hrep₁.some.poincare.pullbackAlong (ptsI g)).L ≅
        (RelEffCartierDiv.ofPoint c₁ x.1 x.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₁ ε₁.1 ε₁.2).idealModule) →
      ∃ Dv : Divisor.degZero (K := k) (F := ↥(ModularCurve.igusaFunctionFieldX1C k M w)),
        (Dv : Divisor k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) =
          Finsupp.single (Mdl₁.pointEquivPlace ⟨x.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact x.2⟩) 1 -
            Finsupp.single (Mdl₁.pointEquivPlace ⟨ε₁.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact ε₁.2⟩) 1 ∧
        θ₁ g = Pic0.mk Dv)

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
      red₁ P = Mdl₁.pointEquivPlace ⟨c.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact c.2⟩) :
    ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p))),

      (∀ P ∈ (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))).support,
        ∃ (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) (ModularCurve.TwoChart.modelTo A (↥K) j))
          (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
          Spec.map (CommRingCat.ofHom O.subtype) ≫ ξ.1 =
            (Mη.pointEquivPlace.symm P).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ∧
          c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
            Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ ξ.1 ∧
          ∀ t, c.1.base t ∉ Set.range (pullback.fst i₁.1 i₂.1).base) →

      ∀ (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) D.toBase),
        (gpts (Pic0.mk Dv)).1 = Spec.map (CommRingCat.ofHom O.subtype) ≫ z.1 →

        ∀ (y : G.J0s),
          (pts y).1 ≫ pullback.fst D.toBase (specMap A k) =
            Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ z.1 →
          (G.proj y).2 = 0 := by sorry
