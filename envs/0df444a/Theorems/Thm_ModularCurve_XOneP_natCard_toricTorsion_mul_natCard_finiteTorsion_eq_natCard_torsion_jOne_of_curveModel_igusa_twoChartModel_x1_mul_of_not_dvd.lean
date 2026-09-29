-- Prove2me | Theorems.Thm_ModularCurve_XOneP_natCard_toricTorsion_mul_natCard_finiteTorsion_eq_natCard_torsion_jOne_of_curveModel_igusa_twoChartModel_x1_mul_of_not_dvd
-- name    : ModularCurve.XOneP.natCard_toricTorsion_mul_natCard_finiteTorsion_eq_natCard_torsion_jOne_of_curveModel_igusa_twoChartModel_x1_mul_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/f0d0cfd2-31fc-5d01-9dee-40278b5899a6
-- title:
--   Toric and finite m-torsion counts for J₁(Mp) at p
-- statement:
--   Fix a prime $p$ and an integer $M$ with $5 \le M$, $M \neq 0$ and $p \nmid M$.
--
--   **Arithmetic setting.** Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, and let $\zeta \in L$ be a primitive $p$-th root of unity. Let $K$ be an intermediate field of the Laurent series field $\mathrm{LaurentSeries}\,L$ over $L$, assumed (`hK`) to be [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield of $\mathrm{LaurentSeries}\,L$ generated over $L$ by the coefficientwise image of the $q$-expansion function field of $X_1(Mp)$ over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with an algebra structure over $L$ making $L$ its fraction field, such that $p$ lies in the maximal ideal of $A$ (`hAp`) and $\zeta$ lies in the image of $A$ (`hζA`), together with an $A$-algebra structure on $K$ compatible with $A \to L \to K$. Let $j \in K$ be nonzero with $j$, viewed in $\mathrm{LaurentSeries}\,L$, equal to the coefficientwise image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular invariant (`hj`). Write $X \to \operatorname{Spec} A$ for the two-chart model [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252), glued from the spectra of the chart algebras of $j$ and of $j^{-1}$, and assumed proper.
--
--   **Special fibre.** Let $k$ be an algebraically closed field of characteristic $p$ with an $A$-algebra structure, and let $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$ be proper, smooth of relative dimension $1$ and geometrically integral. Let $i_1, i_2$ be closed immersions of $C_1$, $C_2$ over $\operatorname{Spec} k$ into the base change $X_k =$ `baseChange A (TwoChart.modelTo A K j) k`. The hypotheses `hcover`, `hred`, `hn`, `hn0` require: every point of $X_k$ lies in the image of $i_1$ or of $i_2$; the scheme-theoretic intersection `pullback i₁.1 i₂.1` is reduced; its number of points is $n$; and $0 < n$.
--
--   **Sections.** Let $\varepsilon$ be a section of $X \to \operatorname{Spec} A$ and $\varepsilon_1$, $\varepsilon_2$ sections of $c_1$, $c_2$, with $\varepsilon_1$ followed by $i_1$ equal to the base change of $\varepsilon$ to $k$ (`hε₁`).
--
--   **Relative Picard data.** Let $D$ be a relative $\mathrm{Pic}^0$ designation for $X \to \operatorname{Spec} A$, that is, a scheme $D.P$ with a structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec} A$ and a section $D.\mathrm{zeroSection}$; `hrep` asserts that $D$ represents, with respect to $\varepsilon$, the sub-Picard condition `algEquivZeroCut`, whose predicate on rigidified line bundles is `FibrewiseAlgEquivZero`: there is a rigidified Poincaré bundle on $X$ over $D.\mathrm{toBase}$ satisfying the predicate, every rigidified line bundle satisfying it on a base $T$ is the pullback of the Poincaré bundle along a unique morphism $T \to D.\mathrm{toBase}$ over $\operatorname{Spec} A$ (up to isomorphism of underlying line bundles), and pullback along the zero section gives the unit bundle. Further, $D.\mathrm{toBase}$ is smooth (`hsm`) and separated (`hsep`); `hreps` asserts the analogous representability for $X_k$ and the base change $D_k$ of $D$, and `hPk` that the corresponding Poincaré bundle is isomorphic to the base change along $A \to k$ of the pullback of the Poincaré bundle of $D$ along the first projection. Likewise $D_1$, $D_2$ are relative $\mathrm{Pic}^0$ designations for $c_1$, $c_2$ with representability hypotheses `hrep₁`, `hrep₂`.
--
--   Let $\nu_2$ be a morphism $D_k.\mathrm{toBase} \to D_2.\mathrm{toBase}$ over $\operatorname{Spec} k$ such that (`hν₂`) for every $k$-scheme $t : T \to \operatorname{Spec} k$ and every $T$-point $a$ of $D_k.\mathrm{toBase}$, the pullback of the Poincaré bundle of $D_2$ along $a$ followed by $\nu_2$ is isomorphic to the rigidification along the section induced by $\varepsilon_2$ of the restriction along the base-changed $i_2$ of the pullback of the Poincaré bundle of `hreps` along $a$; thus $\nu_2$ implements restriction of line bundles to the component $C_2$.
--
--   **Generic fibre over $\overline{\mathbb{Q}}$.** Fix algebra structures of $A$ and of $L$ on $\mathrm{AlgebraicClosure}\,\mathbb{Q}$ forming a scalar tower. Let $M_\eta$ be a curve model over $\mathrm{AlgebraicClosure}\,\mathbb{Q}$ of the field [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) (a proper smooth integral curve whose function field is identified with that field, together with a bijection `placeOfPoint` between its closed points and the places of the field, the stalk condition, and the containment of finite sets of points in affine opens), and let $e_\eta$ be an isomorphism from $M_\eta.C$ to the base change of $X$ to $\mathrm{AlgebraicClosure}\,\mathbb{Q}$ compatible with the structure morphisms (`heη`). The preimage under $e_\eta$ followed by the first projection of the finite chart of $X$ is nonempty, and `hMηpin` asserts that for every element $a$ of the finite chart algebra `chartAlgFin A K j`, the element of `x1FunctionFieldBar (M * p)` obtained from $a$ by the chart identification, the germ at the generic point and $M_\eta.\mathrm{ffEquiv}^{-1}$ has, as a Laurent series over $\mathrm{AlgebraicClosure}\,\mathbb{Q}$, the coefficientwise image under $L \to \mathrm{AlgebraicClosure}\,\mathbb{Q}$ of the Laurent series of $a$. The hypothesis `hgal` requires Galois equivariance of the resulting dictionary: for every $\mathbb{Q}$-automorphism $g$ of $\mathrm{AlgebraicClosure}\,\mathbb{Q}$ fixing the image of $L$ pointwise and all sections $x, x'$ of $M_\eta.\mathrm{toBase}$, if $x'$ followed by $e_\eta$ and the first projection equals $\operatorname{Spec}(g)$ followed by the same composite applied to $x$, then `Mη.pointEquivPlace x'` is the image of `Mη.pointEquivPlace x` under the action of $g$ through [`ModularCurve.arithmeticGalois (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_ArithmeticGalois.html#L54).
--
--   **Special fibre dictionary.** Let $G$ be a [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9): abelian groups $G.J_{0s}$, $G.J_I$, $G.J_E$, a subgroup $G.\mathrm{torus}$ of $G.J_{0s}$, and a surjective homomorphism $G.\mathrm{proj} : G.J_{0s} \to G.J_I \times G.J_E$ with kernel $G.\mathrm{torus}$. Let `pts`, `ptsI`, `ptsE` be bijections from $G.J_{0s}$, $G.J_I$, $G.J_E$ onto the $k$-points of $D_k.\mathrm{toBase}$, $D_1.\mathrm{toBase}$, $D_2.\mathrm{toBase}$ respectively. The hypotheses `hadd`, `haddI`, `haddE` require each bijection to be additive in the Picard sense: the pullback of the relevant Poincaré bundle along the point attached to $a + b$ is isomorphic to the tensor product of the pullbacks along the points attached to $a$ and to $b$. The hypothesis `hproj` requires that for each $x \in G.J_{0s}$ the point `ptsI (G.proj x).1` is `pts x` followed by the morphism $D_k.\mathrm{toBase} \to D_1.\mathrm{toBase}$ induced by pullback of bundles along $i_1$, and `ptsE (G.proj x).2` is `pts x` followed by $\nu_2$.
--
--   **Igusa identification of the components.** Let $w$ be an `IntegralWeightOneForm k M`, consisting of a weight-one modular form on $\Gamma_1(M)$, an integral power series which is its $q$-expansion, and the nonvanishing over $k$ of the reduced series; and let $\mathrm{Mdl}_1$, $\mathrm{Mdl}_2$ be curve models over $k$ of the Igusa function field [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35), with isomorphisms $e_1 : \mathrm{Mdl}_1.C \cong C_1$ and $e_2 : \mathrm{Mdl}_2.C \cong C_2$ compatible with the structure morphisms (`he₁`, `he₂`).
--
--   **Generic dictionary and Abel–Jacobi normalisation.** Let `gpts` be a bijection from [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186), the degree-zero divisor class group of `x1FunctionFieldBar (M * p)` over $\mathrm{AlgebraicClosure}\,\mathbb{Q}$, onto the $\mathrm{AlgebraicClosure}\,\mathbb{Q}$-points of $D.\mathrm{toBase}$, additive for the relative group law attached to `hrep` through `algEquivZeroGroupCut` (`hgadd`). Let `hDL` assert representability for the base change of $X$ and of $D$ to $L$, let $\mathrm{ajL}$ be a morphism from $X_L$ to $D_L.\mathrm{toBase}$ over $\operatorname{Spec} L$, let $kL$ be a morphism from the $\mathrm{AlgebraicClosure}\,\mathbb{Q}$-fibre to the $L$-fibre of $X$, let $\overline{\mathrm{aj}} : M_\eta.C \to D.P$ and let $\overline{\varepsilon}$ be a section of $M_\eta.\mathrm{toBase}$. The hypotheses on these data are: `hPL`, identifying the Poincaré bundle over $L$ with the base change of the pullback of that of $D$; `hajLε`, that $\varepsilon$ followed by $\mathrm{ajL}$ is the zero section of $D_L$; `hajL`, that for every field $K'$, every morphism $t : \operatorname{Spec} K' \to \operatorname{Spec} L$ and every $t$-point $x$ of $X_L$, the pullback of the Poincaré bundle of `hDL` along $x$ followed by $\mathrm{ajL}$ is isomorphic to the line bundle of the relative effective Cartier divisor of the point $x$ tensored with the ideal module of the divisor of the point $t$ followed by the base-changed $\varepsilon$ — so $\mathrm{ajL}$ classifies the class of $[x] - [\varepsilon]$; `hkL₁`, `hkL₂`, compatibility of $kL$ with the two projections and with $\operatorname{Spec} L \to \operatorname{Spec} \mathrm{AlgebraicClosure}\,\mathbb{Q}$; `hajbar`, that $\overline{\mathrm{aj}}$ is $e_\eta$ followed by $kL$, by $\mathrm{ajL}$ and by the first projection of $D$; `hajbar_over`, that $\overline{\mathrm{aj}}$ lies over $M_\eta.\mathrm{toBase}$; `hεbar`, that $\overline{\varepsilon}$ corresponds to $\varepsilon$; `hεbar_aj`, that $\overline{\varepsilon}$ followed by $\overline{\mathrm{aj}}$ is the zero section of $D$; and `hpts_aj`, that for all sections $x, s$ of $M_\eta.\mathrm{toBase}$ with $s$ corresponding to $\varepsilon$ there is a degree-zero divisor $Dv$ on `x1FunctionFieldBar (M * p)` equal to $\mathrm{single}(\text{place of } x) - \mathrm{single}(\text{place of } s)$ such that `gpts` of the class of $Dv$ is $x$ followed by $\overline{\mathrm{aj}}$.
--
--   **The place above $p$.** Let $\mathrm{Pl}$ be a valuation subring of $\mathrm{AlgebraicClosure}\,\mathbb{Q}$ lying over $p$, in the sense that $p$ is a nonunit of $\mathrm{Pl}$ (`hPl`). Let $\rho : A \to \mathrm{Pl}$ be a ring homomorphism whose composite with the inclusion of $\mathrm{Pl}$ is the structure map $A \to \mathrm{AlgebraicClosure}\,\mathbb{Q}$ (`hρ`), and let $\pi_k : \mathrm{Pl} \to k$ be a surjective ring homomorphism with $\pi_k \circ \rho$ equal to the structure map $A \to k$ (`hAlgk`, `hπk`). Finally let $m$ be a positive integer with $p \nmid m$.
--
--   **Conclusion.** Put
--
--   $J$ = the underlying set of the $m$-torsion subgroup [`AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (x1FunctionFieldBar (M * p)) m`](def/AlgebraicCurve_DivisorClassGroup.html#L244) of `JOne (M * p)`;
--
--   $\mathrm{Fin}$ = the set of $x \in J$ for which there exists a morphism $z$ from $\operatorname{Spec} \mathrm{Pl}$ to $D.P$ over $\operatorname{Spec} \rho$ with the $\mathrm{AlgebraicClosure}\,\mathbb{Q}$-point `gpts x` equal to $\operatorname{Spec}(\mathrm{Pl} \hookrightarrow \mathrm{AlgebraicClosure}\,\mathbb{Q})$ followed by $z$;
--
--   $\mathrm{Tor}$ = the set of $x \in J$ for which there exists such a $z$ which moreover satisfies: there is $y \in G.J_{0s}$ with `pts y` followed by the first projection $D_k \to D$ equal to $\operatorname{Spec}(\pi_k)$ followed by $z$, and $G.\mathrm{proj}\, y = 0$.
--
--   Then
--   $$\#\mathrm{Tor} \cdot \#\mathrm{Fin} = \#J,$$
--   the cardinalities being taken as `Nat.card`.
--
--   This is the counting step, at a place of $\overline{\mathbb{Q}}$ above $p$, for the prime-to-$p$ torsion of the Jacobian of $X_1(Mp)$ in its semistable (Deligne–Rapoport) reduction, where the special fibre is a union of two Igusa curves crossing at the supersingular points: the classes killed by $m$ that extend to the valuation ring ('finite part') and those whose reduction lands in the toric part of the special-fibre Picard group satisfy $\#\mathrm{Tor} \cdot \#\mathrm{Fin} = \#J[m]$. It is used by [`ModularCurve.XOneP.exists_forall_exists_eq_smul_sub_of_proj_eq_zero_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_forall_exists_eq_smul_sub_of_proj_eq_zero_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul) in the analysis of the toric and finite parts entering level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_natCard_toricTorsion_mul_natCard_finiteTorsion_eq_natCard_torsion_jOne_of_curveModel_igusa_twoChartModel_x1_mul_of_not_dvd.lean

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
import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.natCard_toricTorsion_mul_natCard_finiteTorsion_eq_natCard_torsion_jOne_of_curveModel_igusa_twoChartModel_x1_mul_of_not_dvd
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

    (w : ModularCurve.IntegralWeightOneForm k M)
    (Mdl₁ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₁ : Mdl₁.C ≅ C₁)
    (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)
    (Mdl₂ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₂ : Mdl₂.C ≅ C₂)
    (he₂ : e₂.hom ≫ c₂ = Mdl₂.toBase)

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

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ) (hπk : Function.Surjective πk)

    (m : ℕ) (hm0 : 0 < m) (hpm : ¬ p ∣ m) :
    let J : Set (ModularCurve.JOne (M * p)) :=
      ↑(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) m)
    let Fin : Set (ModularCurve.JOne (M * p)) := {x | x ∈ J ∧
      ∃ z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
        (gpts x).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z.1}
    let Tor : Set (ModularCurve.JOne (M * p)) := {x | x ∈ J ∧
      ∃ z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
        (gpts x).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z.1 ∧
        ∃ y : G.J0s, (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z.1 ∧ G.proj y = 0}
    Nat.card ↥Tor * Nat.card ↥Fin = Nat.card ↥J := by sorry
