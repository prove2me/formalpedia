-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_toric_nsmul_eq_of_toric_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_toric_nsmul_eq_of_toric_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/0a1cde7e-04a8-5c18-ad86-607610cf8cd9
-- title:
--   Divisibility of toric torsion classes on J₁(Mp)
-- statement:
--   Throughout, $p$ is a prime and $M$ a non-zero natural number with $5 \le M$ and $p \nmid M$ (hypotheses `hM`, `hpM`).
--
--   **Arithmetic data.** $L$ is a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, and $\zeta \in L$ is a primitive $p$-th root of unity. $K$ is an intermediate field of $L \subseteq \operatorname{LaurentSeries} L$, and `hK` requires that $K$ be [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), the subfield generated over $L$ by the coefficientwise image of the $q$-expansion field [`ModularCurve.x1FunctionFieldC ℚ (M * p)`](def/ModularCurve_X1.html#L134) of $X_1(Mp)$ over $\mathbb{Q}$. $A$ is a discrete valuation domain with fraction field $L$ such that $p$ lies in its maximal ideal (`hAp`) and $\zeta$ lies in the image of $A$ in $L$ (`hζA`), and $K$ is an $A$-algebra compatibly with $A \to L \to K$. Finally $j \in K$ is non-zero and its Laurent expansion is the coefficientwise image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), i.e. of $q^{-1}$ times the integral power series `jNumQ` (`hj`). The morphism [`ModularCurve.TwoChart.modelTo A ↥K j`](def/ModularCurve_TwoChartModel.html#L252) from the two-chart model to $\operatorname{Spec} A$, assembled from the subalgebras `chartAlgFin` and `chartAlgInf` of $K$, is assumed proper.
--
--   **Geometry of the fibre over the residue field.** $k$ is an algebraically closed field of characteristic $p$ and an $A$-algebra. Two morphisms $c_1 : C_1 \to \operatorname{Spec} k$ and $c_2 : C_2 \to \operatorname{Spec} k$ are proper, smooth of relative dimension $1$ and geometrically integral, and $i_1$, $i_2$ are closed immersions of $C_1$, $C_2$ over the base change `baseChange A (ModularCurve.TwoChart.modelTo A ↥K j) k`, that is, over the second projection of the pullback of the model along $\operatorname{Spec} k \to \operatorname{Spec} A$. The hypothesis `hcover` states that every point of that pullback lies in the image of $i_1$ or of $i_2$; `hred` states that the scheme-theoretic fibre product of $i_1$ and $i_2$ is reduced; $n$ is its number of points (`hn`) and $0 < n$ (`hn0`).
--
--   **Sections.** $\varepsilon$ is a section of the two-chart model over $\operatorname{Spec} A$, and $\varepsilon_1$, $\varepsilon_2$ are sections of $c_1$, $c_2$; `hε₁` requires that $\varepsilon_1$ followed by $i_1$ be the base-changed section `sectionBaseChange k ε`.
--
--   **Relative $\mathrm{Pic}^0$ data.** $D$ is a `RelativePic0Designation` over $A$ for the two-chart model: a scheme $D.P$ with a structure morphism `D.toBase` to $\operatorname{Spec} A$ and a zero section. The hypothesis `hrep` asserts that $D$, with the cut `algEquivZeroCut` (the condition that a rigidified line bundle be fibrewise algebraically equivalent to zero), is represented, i.e. carries a Poincaré bundle satisfying the universal property and trivial along the zero section; `hsm` and `hsep` require `D.toBase` to be smooth and separated. The hypothesis `hreps` is the corresponding representability statement over $k$ for `D.baseChange k` with the section `sectionBaseChange k ε`, and `hPk` requires its Poincaré bundle to be isomorphic to the base change along `BaseChange.ofR` of the pullback of the Poincaré bundle of `hrep.some` along the first projection of `pullback D.toBase (specMap A k)`. Designations $D_1$, $D_2$ over $k$ for $c_1$, $c_2$ are likewise represented with respect to $\varepsilon_1$, $\varepsilon_2$ (`hrep₁`, `hrep₂`). A morphism $\nu_2$ from the base of `D.baseChange k` to the base of $D_2$ over $k$ is given, subject to `hν₂`: for every $k$-scheme $t : T \to \operatorname{Spec} k$ and every $T$-point $a$ of the base of `D.baseChange k`, the pullback of the Poincaré bundle of `hrep₂.some` along $a$ followed by $\nu_2$ is isomorphic to the rigidification, in the sense of `Scheme.Modules.rigidify` with respect to `rigSection c₂ t ε₂` and `pullback.snd c₂ t`, of the pullback along `curveChange i₂.1 i₂.2 t` of the pullback of the Poincaré bundle of `hreps` along $a$.
--
--   **The generic fibre over $\overline{\mathbb{Q}}$.** Compatible algebra structures $A \to \overline{\mathbb{Q}}$ and $L \to \overline{\mathbb{Q}}$ are fixed. $M\eta$ is a `CurveModel` over $\overline{\mathbb{Q}}$ of the field [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182): a proper smooth integral curve whose function field is identified with that field and whose closed points are in bijection with its places. An isomorphism $e\eta$ from $M\eta.C$ to `pullback (ModularCurve.TwoChart.modelTo A ↥K j) (specMap A (AlgebraicClosure ℚ))` is given, compatible with the structure morphisms (`heη`). The preimage under $e\eta$ followed by the first projection of the image of the finite chart [`ModularCurve.TwoChart.ιFin A ↥K j`](def/ModularCurve_TwoChartModel.html#L231) is non-empty, and `hMηpin` pins down the identification: for every element $a$ of the finite-chart subalgebra [`ModularCurve.TwoChart.chartAlgFin A ↥K j`](def/ModularCurve_TwoChartModel.html#L135), the element of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) obtained from the germ of $a$ on that open, transported by `Mη.ffEquiv.symm`, has Laurent expansion the coefficientwise image along $L \to \overline{\mathbb{Q}}$ of the expansion of $a$. The hypothesis `hgal` is Galois equivariance: for every automorphism $g$ of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ fixing $L$ pointwise, and for all $\overline{\mathbb{Q}}$-points $x$, $x'$ of $M\eta.C$ over its base, if $x'$ followed by $e\eta$ and the first projection equals $\operatorname{Spec}(g)$ followed by the same composite for $x$, then `Mη.pointEquivPlace x'` is the translate of `Mη.pointEquivPlace x` by the action of $g$ through [`ModularCurve.arithmeticGalois (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_ArithmeticGalois.html#L54).
--
--   **Special-fibre group bookkeeping.** $G$ is a [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9): abelian groups `J0s`, `JI`, `JE`, a subgroup `torus` of `J0s`, and a surjective homomorphism `proj : J0s →+ JI × JE` whose kernel is `torus`. Bijections `pts`, `ptsI`, `ptsE` identify `G.J0s`, `G.JI`, `G.JE` with the $k$-points of the bases of `D.baseChange k`, $D_1$, $D_2$ respectively. The hypotheses `hadd`, `haddI`, `haddE` state that each bijection is additive in the sense that the pullback of the relevant Poincaré bundle along the point attached to a sum is isomorphic to the tensor product of the pullbacks along the points attached to the summands. The hypothesis `hproj` states that for every $x \in G.\mathrm{J0s}$ the first component of $\operatorname{proj} x$ corresponds under `ptsI` to `pts x` composed with the morphism `RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some`, and the second component corresponds under `ptsE` to `pts x` composed with $\nu_2$.
--
--   **Igusa identification of the two components.** $w$ is an `IntegralWeightOneForm k M`: a weight-one modular form on $\Gamma_1(M)$ together with an integral power series which is its $q$-expansion and whose reduction to $k$ is non-zero. Curve models $\mathrm{Mdl}_1$, $\mathrm{Mdl}_2$ over $k$ of the field [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35) are given, with isomorphisms $e_1 : \mathrm{Mdl}_1.C \cong C_1$ and $e_2 : \mathrm{Mdl}_2.C \cong C_2$ compatible with the structure morphisms (`he₁`, `he₂`).
--
--   **Abel–Jacobi data.** `gpts` is a bijection from [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186), the group of degree-zero divisor classes of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) modulo principal divisors, onto the points of `D.toBase` over `specMap A (AlgebraicClosure ℚ)`, and `hgadd` requires it to carry addition to the relative group law attached to `hrep.some`. Over $L$, `hDL` is the representability statement for `D.baseChange L`, `ajL` is a morphism from the curve base-changed to $L$ to the base of `D.baseChange L` over $L$, `kL` a morphism from the pullback over $\overline{\mathbb{Q}}$ to the pullback over $L$, `ajbar` a morphism $M\eta.C \to D.P$, and `εbar` a $\overline{\mathbb{Q}}$-point of $M\eta.C$ over its base. These are constrained by: `hPL`, the analogue of `hPk` over $L$; `hajLε`, that the base-changed section followed by `ajL` is the zero section of `D.baseChange L`; `hajL`, that for every field $K'$, every morphism $t : \operatorname{Spec} K' \to \operatorname{Spec} L$ and every $K'$-point $x$ of the curve over $L$, the pullback of the Poincaré bundle of `hDL` along $x$ followed by `ajL` is isomorphic to the line bundle of the relative effective Cartier divisor of the point $x$ tensored with the ideal module of the divisor of $t$ followed by the base-changed section, i.e. to the class of $x - \varepsilon$; `hkL₁`, `hkL₂`, the compatibilities of `kL` with the two projections; `hajbar`, that `ajbar` is $e\eta$ followed by `kL`, `ajL` and the first projection of `pullback D.toBase (specMap A L)`; `hajbar_over`, that `ajbar` followed by `D.toBase` is `Mη.toBase` followed by `specMap A (AlgebraicClosure ℚ)`; `hεbar` and `hεbar_aj`, that `εbar` induces the point $\varepsilon$ and that `εbar` followed by `ajbar` is the zero section; and `hpts_aj`, that for all $\overline{\mathbb{Q}}$-points $x$, $s$ of $M\eta.C$ over its base, if $s$ induces the point $\varepsilon$, then there is a degree-zero divisor $Dv$ equal to the difference of the single divisors at `Mη.pointEquivPlace x` and `Mη.pointEquivPlace s` with coefficient $1$, whose class under `gpts` is $x$ followed by `ajbar`.
--
--   **Valuation subring.** $Pl$ is a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit in it (`hPl`), $\rho : A \to Pl$ is a ring homomorphism whose composition with the inclusion $Pl \hookrightarrow \overline{\mathbb{Q}}$ is the structure map of $A$ (`hρ`), and $\pi_k : Pl \to k$ is a surjective ring homomorphism with $\pi_k \circ \rho$ the structure map $A \to k$ (`hAlgk`, `hπk`).
--
--   **Multipliers.** $m$ and $d$ are positive natural numbers with $p \nmid m d$.
--
--   **Conclusion.** For every class $x \in \mathrm{JOne}(Mp)$ with $m \cdot x = 0$, every point $z$ of `D.toBase` over $\operatorname{Spec}(\rho)$ and every $y \in G.\mathrm{J0s}$ such that the point `gpts x` equals $\operatorname{Spec}(Pl \hookrightarrow \overline{\mathbb{Q}})$ followed by $z$, such that `pts y` followed by the first projection `pullback.fst D.toBase (specMap A k)` equals $\operatorname{Spec}(\pi_k)$ followed by $z$, and such that $G.\mathrm{proj}\, y = 0$, there exist a class $x' \in \mathrm{JOne}(Mp)$, a point $z'$ of `D.toBase` over $\operatorname{Spec}(\rho)$ and an element $y' \in G.\mathrm{J0s}$ with all of the following: $(md) \cdot x' = 0$; the point `gpts x'` equals $\operatorname{Spec}(Pl \hookrightarrow \overline{\mathbb{Q}})$ followed by $z'$; `pts y'` followed by `pullback.fst D.toBase (specMap A k)` equals $\operatorname{Spec}(\pi_k)$ followed by $z'$; $G.\mathrm{proj}\, y' = 0$; and $d \cdot x' = x$.
--
--   Thus a class of order dividing $m$ which is toric, in the sense of admitting a $Pl$-valued lift whose reduction lies in the kernel of $G.\mathrm{proj}$, equals $d$ times a toric class of order dividing $md$.
--
--   This is the divisibility step for the toric part of the special fibre of the Jacobian of $X_1(Mp)$ at $p$: classes of order prime to $p$ whose $Pl$-valued extension reduces into the kernel of the projection to the two components of the special fibre are divisible by any integer $d$ prime to $p$ within the toric torsion classes. It is used by [`ModularCurve.XOneP.exists_forall_exists_eq_smul_sub_of_proj_eq_zero_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_forall_exists_eq_smul_sub_of_proj_eq_zero_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul) in the analysis of the component and toric structure of $J_1(Mp)$ at $p$ that underlies level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_toric_nsmul_eq_of_toric_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul.lean

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

theorem ModularCurve.XOneP.exists_toric_nsmul_eq_of_toric_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul
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
    (m d : ℕ) (hm0 : 0 < m) (hd0 : 0 < d) (hpmd : ¬ p ∣ m * d) :
    ∀ (x : ModularCurve.JOne (M * p)), m • x = 0 →
      ∀ (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y : G.J0s), (gpts x).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z.1 → (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z.1 → G.proj y = 0 →
        ∃ (x' : ModularCurve.JOne (M * p)) (z' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y' : G.J0s),
          (m * d) • x' = 0 ∧ (gpts x').1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z'.1 ∧ (pts y').1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z'.1 ∧ G.proj y' = 0 ∧ d • x' = x := by sorry
