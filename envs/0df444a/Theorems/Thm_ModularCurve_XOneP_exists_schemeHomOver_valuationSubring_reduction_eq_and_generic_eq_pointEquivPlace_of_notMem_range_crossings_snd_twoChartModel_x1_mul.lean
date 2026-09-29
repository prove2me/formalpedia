-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_schemeHomOver_valuationSubring_reduction_eq_and_generic_eq_pointEquivPlace_of_notMem_range_crossings_snd_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_schemeHomOver_valuationSubring_reduction_eq_and_generic_eq_pointEquivPlace_of_notMem_range_crossings_snd_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/f605d809-1b80-5291-ad3b-d4097750e667
-- title:
--   Hensel lifting of off-crossing k-points of the second component
-- statement:
--   Throughout, the following data are fixed.
--
--   *Arithmetic input.* A prime $p$; a natural number $M$ with $5 \le M$ and $p \nmid M$; a field $L$ of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, together with a primitive $p$-th root of unity $\zeta \in L$; an intermediate field $K$ of $L \subseteq \mathrm{LaurentSeries}\,L$ with $K =$ [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield of $L((q))$ generated over $L$ by the coefficientwise image of the function field of $X_1(Mp)$ over $\mathbb{Q}$; a discrete valuation ring $A$ which is a domain with fraction field $L$, such that $p$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A$; and an element $j \in K$, assumed nonzero, whose image in $\mathrm{LaurentSeries}\,L$ is the coefficientwise image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular invariant. The scheme under study is the two-chart model [`ModularCurve.TwoChart.modelTo A ↥K j`](def/ModularCurve_TwoChartModel.html#L252), written $X \to \operatorname{Spec} A$ below, glued from the finite and infinite chart algebras attached to $j$; $K$ is an $A$-algebra compatibly with $L$.
--
--   *Geometric special fibre.* An algebraically closed field $k$ of characteristic $p$ which is an $A$-algebra; two schemes $C_1, C_2$ with morphisms $c_1 : C_1 \to \operatorname{Spec} k$ and $c_2 : C_2 \to \operatorname{Spec} k$, each proper, smooth of relative dimension $1$ and geometrically integral; closed immersions $i_1 : C_1 \to X \times_A k$ and $i_2 : C_2 \to X \times_A k$ over $k$; the hypothesis `hcover`, that every point of $X \times_A k$ lies in the image of $i_1$ or of $i_2$; the hypothesis `hred`, that the scheme-theoretic intersection $C_1 \times_{X \times_A k} C_2$ is reduced; and a natural number $n > 0$ equal to the cardinality of that intersection.
--
--   *Sections.* A section $\varepsilon$ of $X \to \operatorname{Spec} A$, sections $\varepsilon_1$ of $c_1$ and $\varepsilon_2$ of $c_2$, and the hypothesis `hε₁` that $\varepsilon_1$ followed by $i_1$ is the base change of $\varepsilon$ to $k$.
--
--   *Relative Picard data.* Relative $\mathrm{Pic}^0$ designations $D$ for $X \to \operatorname{Spec} A$ (a scheme with a structure morphism to $\operatorname{Spec} A$ and a zero section), $D_1$ for $c_1$ and $D_2$ for $c_2$, each equipped with a representability datum `RepresentsRelSubPic` for the cut of fibrewise algebraically-trivial rigidified line bundles: a Poincaré bundle lying in the cut, the universal property that every such rigidified bundle on a base $T$ is induced by a unique $T$-point, and triviality along the zero section. Further: smoothness and separatedness of $D \to \operatorname{Spec} A$; a representability datum `hreps` for the base change of $D$ to $k$; the hypothesis `hPk`, that the Poincaré bundle of `hreps` is isomorphic to the base change to $k$ of the pullback of the Poincaré bundle of $D$ along the first projection; a morphism $\nu_2$ from the base of $D \times_A k$ to the base of $D_2$; and the hypothesis `hν₂`, that for every $k$-scheme $T$ and every $T$-point $a$ of $D \times_A k$ the pullback of the Poincaré bundle of $D_2$ along $a$ followed by $\nu_2$ is isomorphic to the rigidification, along the section of $c_2$ determined by $\varepsilon_2$, of the pullback under the curve-change morphism of the bundle obtained from `hreps` by pulling back along $a$.
--
--   *Properness and embeddings.* $X \to \operatorname{Spec} A$ is proper; $A$ and $L$ are algebras over $\mathrm{AlgebraicClosure}\,\mathbb{Q}$-target, i.e. algebra structures $A \to \overline{\mathbb{Q}}$ and $L \to \overline{\mathbb{Q}}$ are fixed compatibly.
--
--   *Generic geometric model.* A curve model $M_\eta$ over $\overline{\mathbb{Q}}$ for the function field [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) (a scheme $M_\eta.C$, proper and smooth of relative dimension $1$ over $\overline{\mathbb{Q}}$, with an isomorphism of its function field with that field and a bijection between its closed points and the places); an isomorphism $e_\eta : M_\eta.C \to X \times_A \overline{\mathbb{Q}}$ compatible with the structure morphisms (`heη`); nonemptiness of the preimage under $e_\eta$ followed by the first projection of the image of the finite chart; the hypothesis `hMηpin`, that for every element $a$ of the finite chart algebra the function-field element obtained from $a$ by restriction along $e_\eta$ followed by the first projection has Laurent expansion equal to the coefficientwise image under $L \to \overline{\mathbb{Q}}$ of the expansion of $a$; and the hypothesis `hgal`, that for every automorphism $g$ of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ fixing the image of $L$, and all $\overline{\mathbb{Q}}$-points $x, x'$ of $M_\eta.C$ with $x'$ equal to $g$-conjugation applied to $x$ in the chart, the place attached to $x'$ is the image of the place attached to $x$ under the semilinear action [`ModularCurve.arithmeticGalois`](def/ModularCurve_ArithmeticGalois.html#L54) of $g$.
--
--   *Néron special-fibre dictionary.* An object $G$ of [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9) (abelian groups $G.J_{0s}$, $G.J_I$, $G.J_E$, a subgroup `torus` of $G.J_{0s}$, and a surjective homomorphism $G.\mathrm{proj} : G.J_{0s} \to G.J_I \times G.J_E$ with kernel `torus`); bijections `pts`, `ptsI`, `ptsE` of $G.J_{0s}$, $G.J_I$, $G.J_E$ with the $k$-points of the bases of $D \times_A k$, $D_1$, $D_2$ respectively; the hypotheses `hadd`, `haddI`, `haddE`, that each of these bijections turns addition into tensor product of the corresponding pullbacks of the Poincaré bundles; and `hproj`, that for every $x \in G.J_{0s}$ the point `ptsI (G.proj x).1` is obtained from `pts x` by postcomposition with the morphism `RepresentsRelSubPic.pullbackHom` attached to $i_1$, and `ptsE (G.proj x).2` by postcomposition with $\nu_2$.
--
--   *Generic points and Hecke action.* A bijection `gpts` of $J_1(Mp)(\overline{\mathbb{Q}}) = \mathrm{Pic}^0(\overline{\mathbb{Q}}, \mathrm{x1FunctionFieldBar}(Mp))$ with the $\overline{\mathbb{Q}}$-points of the base of $D$ over $\operatorname{Spec} A$, additive for the relative group law of $D$ (`hgadd`); a map $\varphi$ from [`ModularCurve.HeckeAlgOne`](def/ModularCurve_X1HeckeModule.html#L16) to endomorphisms of the base of $D$ over $\operatorname{Spec} A$ which is additive for the relative group law in the sense of `hφmul`, and which transports the Hecke action on $J_1(Mp)$ through `gpts` (`hφpts`).
--
--   *Abel–Jacobi data over $L$ and $\overline{\mathbb{Q}}$.* A representability datum `hDL` for the base change of $D$ to $L$; a morphism $\mathrm{ajL}$ from $X \times_A L$ to the base of $D \times_A L$ over $L$; a comparison morphism $kL : X \times_A \overline{\mathbb{Q}} \to X \times_A L$ with the two projection compatibilities `hkL₁`, `hkL₂`; a morphism $\overline{\mathrm{aj}} : M_\eta.C \to D.P$ defined by `hajbar` as $e_\eta$ followed by $kL$, $\mathrm{ajL}$ and the first projection, and lying over the structure morphisms (`hajbar_over`); a $\overline{\mathbb{Q}}$-point $\overline{\varepsilon}$ of $M_\eta.C$ with `hεbar` (it corresponds to $\varepsilon$ in the chart) and `hεbar_aj` (it is carried by $\overline{\mathrm{aj}}$ to the zero section); the hypothesis `hPL` comparing the Poincaré bundle of `hDL` with the base change to $L$ of the pullback of that of $D$; `hajLε`, that the base-changed section $\varepsilon$ is carried by $\mathrm{ajL}$ to the zero section; `hajL`, the Abel–Jacobi property that for every field $K'$, every $K'$-point $x$ of $X \times_A L$ over $\operatorname{Spec} L$, the pullback of the Poincaré bundle of `hDL` along $x$ followed by $\mathrm{ajL}$ is isomorphic to the line bundle of the relative effective Cartier divisor of the point $x$ tensored with the ideal module of the divisor of the section $\varepsilon$; and `hpts_aj`, that for all $\overline{\mathbb{Q}}$-points $x$ and $s$ of $M_\eta.C$ with $s$ corresponding to $\varepsilon$, there is a degree-zero divisor $D_v$ equal to $[\,\text{place of } x\,] - [\,\text{place of } s\,]$ whose class satisfies $\mathrm{gpts}(\mathrm{Pic}^0\text{-class of } D_v) = x$ followed by $\overline{\mathrm{aj}}$.
--
--   *Igusa component.* An integral weight-one form $w$ of level $M$ over $k$ (a modular form of weight $1$ on $\Gamma_1(M)$ with an integral $q$-expansion whose reduction is nonzero); a curve model $\mathrm{Mdl}_1$ over $k$ for the Igusa function field [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35), an isomorphism $e_1 : \mathrm{Mdl}_1.C \cong C_1$ over $k$ (`he₁`), nonemptiness of the relevant chart preimage, and the hypothesis `hgauss₁`, that for every element $a$ of the finite chart algebra and all power series $x, y$ over $A$ with $y$ having nonzero reduction and $a \cdot y = x$ as Laurent series over $L$, the corresponding element of the Igusa function field has Laurent expansion the quotient of the reductions of $x$ and $y$; an isomorphism of abelian groups $\theta_1 : G.J_I \cong \mathrm{Pic}^0(k, \mathrm{igusaFunctionFieldX1C}\,k\,M\,w)$ with the compatibility `hθpin₁` expressing $\theta_1(g)$ as the class of a difference of two places whenever the pullback of the Poincaré bundle of $D_1$ along `ptsI g` is isomorphic to the line bundle of a point divisor tensored with the ideal module of $\varepsilon_1$; and a semilinear automorphism $\mathrm{frobIg}$ of the Igusa function field acting on Laurent coefficients by $p$-th powers (`hfrobIg`).
--
--   *Subgroup-scheme data.* A scheme $\mathcal{A}$ with a morphism $a : \mathcal{A} \to \operatorname{Spec} A$ and a morphism $\iota$ from $\mathcal{A}$ to the base of $D$ over $a$, with: $\iota$ a closed immersion; $a$ proper and smooth; all geometric fibres of $a$ connected (`h𝒜conn`); `h𝒜grp`, that the image of $\iota$ on points over any base contains the unit of the relative group law of $D$ and is stable under its multiplication and inversion; `h𝒜gen`, that a class $x \in J_1(Mp)(\overline{\mathbb{Q}})$ lies in [`ModularCurve.normFreePartAt (M * p) p`](def/ModularCurve_X1PrimitiveSpecializationAtP.html#L29) if and only if `gpts x` factors through $\iota$; and `h𝒜hecke`, that the image of $\iota$ on points is stable under each $\varphi(t)$.
--
--   *Valuation-theoretic data.* A valuation subring $\mathrm{Pl}$ of $\overline{\mathbb{Q}}$ lying over $p$ (that is, $p$ is a non-unit of $\mathrm{Pl}$); a ring homomorphism $\rho : A \to \mathrm{Pl}$ whose composite with the inclusion $\mathrm{Pl} \subseteq \overline{\mathbb{Q}}$ is the structure map $A \to \overline{\mathbb{Q}}$; a subring $O \le \mathrm{Pl}$ together with $\rho_O : A \to O$ whose composite with the inclusion is again $A \to \overline{\mathbb{Q}}$; and a surjective ring homomorphism $\pi_k : \mathrm{Pl} \to k$ with $\pi_k \circ \rho$ equal to the structure map $A \to k$.
--
--   Under these hypotheses the assertion is the following. Let $c$ be a $k$-point of $C_2$, that is a section of $c_2$, and assume that for every point $t$ of $\operatorname{Spec} k$ the image $c(t)$ avoids the image of the second projection $C_1 \times_{X \times_A k} C_2 \to C_2$, so that $c$ does not meet the crossings. Then there exist a morphism $\xi : \operatorname{Spec} \mathrm{Pl} \to X$ whose composite with $X \to \operatorname{Spec} A$ is $\operatorname{Spec}(\rho)$, and a place $P$ of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) over $\overline{\mathbb{Q}}$, such that both of the following hold:
--
--   first, $c$ followed by $i_2$ and by the first projection $X \times_A k \to X$ equals $\operatorname{Spec}(\pi_k)$ followed by $\xi$; that is, $\xi$ reduces modulo the maximal ideal of $\mathrm{Pl}$ to the given $k$-point $c$ of the second component;
--
--   second, $\operatorname{Spec}$ of the inclusion $\mathrm{Pl} \subseteq \overline{\mathbb{Q}}$ followed by $\xi$ equals the $\overline{\mathbb{Q}}$-point $M_\eta.\mathrm{pointEquivPlace}^{-1}(P)$ of $M_\eta.C$ followed by $e_\eta$ and by the first projection $X \times_A \overline{\mathbb{Q}} \to X$; that is, the generic fibre of $\xi$ is the $\overline{\mathbb{Q}}$-point of the generic geometric model corresponding to the place $P$.
--
--   This is the Hensel-lifting step for the second (étale, Igusa-type) component of the geometric special fibre of the two-chart model of $X_1(Mp)$ over the discrete valuation ring $A$: a $k$-point off the crossing locus is realised as the reduction of a point with values in a valuation ring of $\overline{\mathbb{Q}}$ above $p$, whose generic fibre is described by a place of the geometric function field. It is used, together with its counterpart for the first component, in the computation of the reduction of divisor classes and of the action of Frobenius and of the Hecke operators on the special fibre of $J_1(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_schemeHomOver_valuationSubring_reduction_eq_and_generic_eq_pointEquivPlace_of_notMem_range_crossings_snd_twoChartModel_x1_mul.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.exists_schemeHomOver_valuationSubring_reduction_eq_and_generic_eq_pointEquivPlace_of_notMem_range_crossings_snd_twoChartModel_x1_mul
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

    (hπk : Function.Surjective ⇑πk) :
    ∀ (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂),

      (∀ t, c.1.base t ∉ Set.range (pullback.snd i₁.1 i₂.1).base) →
      ∃ (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j))
        (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p))),

        c.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
          Spec.map (CommRingCat.ofHom πk) ≫ ξ.1 ∧

        Spec.map (CommRingCat.ofHom Pl.subtype) ≫ ξ.1 =
          (Mη.pointEquivPlace.symm P).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) := by sorry
