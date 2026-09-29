-- Prove2me | Theorems.Thm_ModularCurve_XOneP_addEquiv_proj_fst_eq_pic0Mk_conorm_laurentPlaceReduction_of_points_of_gaussReading_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.addEquiv_proj_fst_eq_pic0Mk_conorm_laurentPlaceReduction_of_points_of_gaussReading_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/03d27ad1-2744-53c0-a1f1-bc200d7ff9bc
-- title:
--   q-expansion pin for the Igusa component of J₁(Mp) at p
-- statement:
--   **Arithmetic data.** Fixed are a prime $p$, a natural number $M$ with $5 \le M$ and $p \nmid M$, a field $L$ of characteristic zero that is a cyclotomic extension of $\mathbb Q$ of conductor $p$, a primitive $p$-th root of unity $\zeta \in L$, and an intermediate field $K$ of the Laurent series field $L((q))$ over $L$ which is required (hypothesis `hK`) to be [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), the subfield of $L((q))$ generated over $L$ by the coefficientwise images of the $q$-expansions forming the function field of $X_1(Mp)$ over $\mathbb Q$. Further, $A$ is a discrete valuation domain with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A$ in $L$, together with an $A$-algebra structure on $K$ compatible with that of $L$; and $j \in K$ is a nonzero element whose underlying Laurent series is the coefficientwise image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157). The two-chart model [`ModularCurve.TwoChart.modelTo A ↥K j`](def/ModularCurve_TwoChartModel.html#L252) of $X_1(Mp)$ over $\mathrm{Spec}\,A$, obtained by glueing the spectra of the finite and infinite chart algebras, is assumed proper. Also fixed are an algebraically closed field $k$ of characteristic $p$ which is an $A$-algebra, and an algebraic closure of $\mathbb Q$ equipped with compatible $A$- and $L$-algebra structures.
--
--   **Special-fibre geometry over $k$ (group `C₁`, `C₂`, `i₁`, `i₂`, `hcover`, `hred`, `hn`, `hn0`).** Two proper, smooth of relative dimension one, geometrically integral schemes $c_1 : C_1 \to \mathrm{Spec}\,k$ and $c_2 : C_2 \to \mathrm{Spec}\,k$ are given with closed immersions $i_1, i_2$ into the base change of the two-chart model to $k$, over that base change; every point of this base change lies in the image of $i_1$ or of $i_2$; the scheme-theoretic intersection `pullback i₁.1 i₂.1` is reduced, and its underlying set has cardinality $n$ with $n > 0$.
--
--   **Sections (`ε`, `ε₁`, `ε₂`, `hε₁`).** A section $\varepsilon$ of the two-chart model over $\mathrm{Spec}\,A$, sections $\varepsilon_1, \varepsilon_2$ of $c_1, c_2$ over $\mathrm{Spec}\,k$, and the requirement that $\varepsilon_1$ followed by $i_1$ is the section obtained from $\varepsilon$ by base change to $k$.
--
--   **Relative $\mathrm{Pic}^0$ data (`D`, `hrep`, `hsm`, `hsep`, `hreps`, `hPk`, `D₁`, `hrep₁`, `D₂`, `hrep₂`, `ν₂`, `hν₂`).** $D$ is a relative $\mathrm{Pic}^0$-designation for the two-chart model over $A$ (a scheme $D.P$ with structure morphism $D.\mathrm{toBase}$ to $\mathrm{Spec}\,A$ and a zero section), and `hrep` asserts that $D$ represents, with respect to $\varepsilon$ and the cut `algEquivZeroCut` (the condition that a rigidified line bundle be fibrewise algebraically equivalent to zero), the associated relative sub-Picard functor: there is a Poincaré rigidified bundle satisfying the cut, universal for that cut, and trivial along the zero section. The morphism $D.\mathrm{toBase}$ is assumed smooth and separated. The hypothesis `hreps` is the corresponding representability statement for the base change of $D$ to $k$ relative to the base-changed curve and section, and `hPk` asserts that its Poincaré bundle is isomorphic to the base change to $k$ (via `BaseChange.ofR`) of the pullback of the Poincaré bundle of `hrep.some` along the first projection of $D.\mathrm{toBase} \times_{\mathrm{Spec} A} \mathrm{Spec}\,k$. Likewise $D_1$ and $D_2$ are relative $\mathrm{Pic}^0$-designations for $c_1$ and $c_2$ over $k$, representing the corresponding functors with respect to $\varepsilon_1$, $\varepsilon_2$ (`hrep₁`, `hrep₂`). Finally $\nu_2$ is a morphism over $k$ from the base change of $D$ to $D_2.\mathrm{toBase}$ such that, for every $k$-scheme $t : T \to \mathrm{Spec}\,k$ and every point $a$ of the base change of $D$ over $t$, the pullback of the Poincaré bundle of `hrep₂.some` along $a$ followed by $\nu_2$ is isomorphic to the rigidification, along `rigSection c₂ t ε₂` and the projection $\mathrm{pullback.snd}\,c_2\,t$, of the pullback along `curveChange i₂` of the pullback of the Poincaré bundle of `hreps` along $a$.
--
--   **The generic curve over $\overline{\mathbb Q}$ (`Mη`, `eη`, `heη`, `Mη_chart_nonempty`, `hMηpin`, `hgal`).** $M_\eta$ is a curve model over $\overline{\mathbb Q}$ for [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) (a proper smooth integral curve with its function field identified with that field, together with the bijection between closed points and places), $e_\eta$ is an isomorphism from $M_\eta.C$ onto the base change of the two-chart model to $\overline{\mathbb Q}$ compatible with the structure morphisms, the preimage under $e_\eta$ followed by the first projection of the open image of the finite chart is nonempty, and the $q$-expansion pin `hMηpin` states that for every element $a$ of the finite chart algebra the function-field element obtained by transporting $a$ through that chart and taking its germ has underlying Laurent series the coefficientwise image along $L \to \overline{\mathbb Q}$ of the Laurent series of $a$. The hypothesis `hgal` is Galois equivariance of the point–place dictionary: for every $\mathbb Q$-algebra automorphism $g$ of $\overline{\mathbb Q}$ fixing the image of $L$ pointwise and all $\overline{\mathbb Q}$-points $x, x'$ of $M_\eta.C$ over the base, if $x'$ followed by $e_\eta$ and the first projection equals $\mathrm{Spec}(g)$ followed by the same composite for $x$, then $M_\eta.\mathrm{pointEquivPlace}\,x'$ is the image of $M_\eta.\mathrm{pointEquivPlace}\,x$ under the semilinear automorphism [`ModularCurve.arithmeticGalois (x1FunctionField (M * p)) g`](def/ModularCurve_ArithmeticGalois.html#L54).
--
--   **Néron special-fibre group data (`G`, `pts`, `ptsI`, `ptsE`, `hadd`, `haddI`, `haddE`, `hproj`).** $G$ is a [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9): abelian groups $J^0_s$, $J_I$, $J_E$, a subgroup `torus` of $J^0_s$, and a surjective homomorphism $\mathrm{proj} : J^0_s \to J_I \times J_E$ with kernel `torus`. Bijections `pts`, `ptsI`, `ptsE` identify $J^0_s$, $J_I$, $J_E$ with the $k$-points of the base change of $D$, of $D_1.\mathrm{toBase}$, of $D_2.\mathrm{toBase}$ respectively; `hadd`, `haddI`, `haddE` state that each dictionary is additive in the sense that the Poincaré pullback along a sum of points is isomorphic to the tensor product of the pullbacks; and `hproj` states that for each $x \in J^0_s$ the point $\mathrm{ptsI}\,(\mathrm{proj}\,x)_1$ is $\mathrm{pts}\,x$ followed by the classifying morphism `RepresentsRelSubPic.pullbackHom` attached to $i_1$, while $\mathrm{ptsE}\,(\mathrm{proj}\,x)_2$ is $\mathrm{pts}\,x$ followed by $\nu_2$.
--
--   **Abel–Jacobi data over $L$ and $\overline{\mathbb Q}$ (`gpts`, `hgadd`, `hDL`, `ajL`, `kL`, `ajbar`, `εbar`, `hPL`, `hajLε`, `hajL`, `hkL₁`, `hkL₂`, `hajbar`, `hajbar_over`, `hεbar`, `hεbar_aj`, `hpts_aj`).** A bijection `gpts` identifies $\mathrm{Pic}^0$ of `x1FunctionFieldBar (M * p)` over $\overline{\mathbb Q}$ with the $\overline{\mathbb Q}$-points of $D.\mathrm{toBase}$ over $\mathrm{Spec}\,A$, and `hgadd` says it is additive for the relative group law attached to `hrep.some` and the cut `algEquivZeroGroupCut`. Over $L$: `hDL` is the representability of the base change of $D$ to $L$, $\mathrm{ajL}$ is a morphism from the curve base-changed to $L$ to the base change of $D$, over $L$, with $\varepsilon$ composed into it equal to the zero section (`hajLε`); `hPL` is the analogue of `hPk` over $L$; and `hajL` is the Abel–Jacobi property of $\mathrm{ajL}$: for every field $K'$, every morphism $t : \mathrm{Spec}\,K' \to \mathrm{Spec}\,L$ and every $K'$-point $x$ of the base-changed curve, the pullback of the Poincaré bundle of `hDL` along $x$ followed by $\mathrm{ajL}$ is isomorphic to the line bundle of the relative effective Cartier divisor of the point $x$ tensored with the ideal module of the divisor of the base-changed section. The morphism $\mathrm{kL}$ relates the base changes to $\overline{\mathbb Q}$ and to $L$ (hypotheses `hkL₁`, `hkL₂` fix it on the two projections); $\overline{\mathrm{aj}}$ is defined by `hajbar` to be $e_\eta$ followed by $\mathrm{kL}$, $\mathrm{ajL}$ and the first projection of $D.\mathrm{toBase} \times \mathrm{Spec}\,L$, and lies over the base by `hajbar_over`; $\overline\varepsilon$ is a $\overline{\mathbb Q}$-point of $M_\eta.C$ which induces the point coming from $\varepsilon$ (`hεbar`) and satisfies $\overline\varepsilon$ followed by $\overline{\mathrm{aj}}$ equal to the zero section (`hεbar_aj`). The hypothesis `hpts_aj` couples `gpts` with $\overline{\mathrm{aj}}$: for all $\overline{\mathbb Q}$-points $x, s$ of $M_\eta.C$ over the base with $s$ induced by $\varepsilon$, there is a degree-zero divisor $D_v$ on `x1FunctionFieldBar (M * p)` whose underlying divisor is $(\text{place of } x) - (\text{place of } s)$ and with $\mathrm{gpts}([D_v])$ equal, as a morphism, to $x$ followed by $\overline{\mathrm{aj}}$.
--
--   **The Igusa component (`w`, `Mdl₁`, `e₁`, `he₁`, `hne₁`, `hgauss₁`, `θ₁`, `hθpin₁`).** $w$ is an integral weight-one form on $\Gamma_1(M)$ over $k$ (a weight-one modular form together with an integral $q$-expansion power series whose reduction over $k$ is nonzero), $\mathrm{Mdl}_1$ a curve model over $k$ for the Igusa field [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35), and $e_1$ an isomorphism $\mathrm{Mdl}_1.C \cong C_1$ compatible with the structure morphisms; the relevant chart preimage is nonempty. The Gauss-reading hypothesis `hgauss₁` states: for every element $a$ of the finite chart algebra and all power series $x, y$ over $A$ with $y$ having nonzero reduction over $k$, if the Laurent series of $a$ times the image of $y$ in $L((q))$ equals the image of $x$, then the element of the Igusa field obtained by transporting $a$ along $e_1$, $i_1$ and the first projection has underlying Laurent series the quotient of the reductions of $x$ and $y$ in $k((q))$. Finally $\theta_1$ is an isomorphism of abelian groups from $J_I$ onto $\mathrm{Pic}^0$ of the Igusa field over $k$, and `hθpin₁` is its Abel–Jacobi characterisation: for $g \in J_I$ and any $k$-point $x$ of $c_1$, if the pullback of the Poincaré bundle of `hrep₁.some` along $\mathrm{ptsI}\,g$ is isomorphic to the line bundle of the divisor of $x$ tensored with the ideal module of the divisor of $\varepsilon_1$, then there is a degree-zero divisor $D_v$ equal to the difference of the places of $x$ and of $\varepsilon_1$ (transported through $e_1^{-1}$) with $\theta_1 g = [D_v]$.
--
--   **Places and reduction maps (`Pl`, `hPl`, `ρ`, `hρ`, `O`, `hO`, `ρO`, `hρO`, `πk`, `hAlgk`).** $\mathrm{Pl}$ is a valuation subring of $\overline{\mathbb Q}$ with $p$ a nonunit in it, $\rho : A \to \mathrm{Pl}$ a ring homomorphism inducing the structure map $A \to \overline{\mathbb Q}$, $O$ a subring of $\overline{\mathbb Q}$ contained in $\mathrm{Pl}$ with a homomorphism $\rho_O : A \to O$ inducing the same structure map, and $\pi_k : \mathrm{Pl} \to k$ a ring homomorphism with $A \to k$ equal to $\pi_k \circ \rho$.
--
--   **Conclusion.** For every map $r_1$ from places of `laurentBaseChange (AlgebraicClosure ℚ) (x1FunctionField M)` to places of `x1FunctionFieldC k M` which is a Laurent place reduction for $(\mathrm{Pl}, \pi_k)$ — that is, it preserves degrees and, for every Laurent series $y$ over $\mathrm{Pl}$ lying in the first field and with nonzero reduction lying in the second, carries the divisor of $y$ to the divisor of its reduction — and under the hypothesis that principal divisors of the first field lie in the subgroup generated by the divisors of such integral Laurent series; for every $\overline{\mathbb Q}$-algebra map $\iota$ from that field to `x1FunctionFieldBar (M * p)` whose underlying ring map is integral, and every $k$-algebra map $\bar\iota$ from `x1FunctionFieldC k M` to the Igusa field `igusaFunctionFieldX1C k M w` whose underlying ring map is integral, both being $q$-expansion inclusions (they preserve the underlying Laurent series); for every degree-zero divisor $D_1$ on `laurentBaseChange (AlgebraicClosure ℚ) (x1FunctionField M)` (this binder re-uses the name of the $\mathrm{Pic}^0$-designation for $c_1$) and every degree-zero divisor $D_\eta$ on `x1FunctionFieldBar (M * p)` such that $D_\eta$ is the conorm of $D_1$ along $\iota$, i.e. $D_\eta(w) = e(w \mid \iota)\, D_1(w|_\iota)$ for every place $w$; for every point $z$ of $D.\mathrm{toBase}$ over $\mathrm{Spec}(\rho_O)$ such that the morphism $\mathrm{gpts}([D_\eta])$ equals $\mathrm{Spec}$ of the inclusion $O \hookrightarrow \overline{\mathbb Q}$ followed by $z$; for every $y \in J^0_s$ whose associated point, composed with the first projection of $D.\mathrm{toBase} \times_{\mathrm{Spec} A} \mathrm{Spec}\,k$, equals $\mathrm{Spec}$ of $\pi_k$ composed with the inclusion $O \hookrightarrow \mathrm{Pl}$, followed by $z$; and for every degree-zero divisor $\overline D$ on the Igusa field which is the conorm along $\bar\iota$ of the pushforward $\mathrm{Finsupp.mapDomain}\,r_1\,D_1$: it follows that
--   $$\theta_1\bigl((\mathrm{proj}\,y)_1\bigr) = [\overline D]$$
--   in $\mathrm{Pic}^0$ of the Igusa field over $k$.
--
--   This is the $q$-expansion pin for the cuspidal Igusa component of the Néron special fibre of $J_1(Mp)$ at $p$: a class on $X_1(M)$ pulled back to $X_1(Mp)$ in characteristic zero, extended over the valuation ring and reduced, is computed on the Igusa component as the pull-back along the Igusa covering of the Deuring reduction of the original divisor. It is used by the statements assembling the pinned Igusa specialisation data of the norm-free part of $J_1(Mp)$, in particular the computation of the first component of the $\mathrm{Pic}^0$-pair and the vanishing criterion for the associated pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_addEquiv_proj_fst_eq_pic0Mk_conorm_laurentPlaceReduction_of_points_of_gaussReading_twoChartModel_x1_mul.lean

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
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_ModularCurve_QExpSemistableSpecializationPinned

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem ModularCurve.XOneP.addEquiv_proj_fst_eq_pic0Mk_conorm_laurentPlaceReduction_of_points_of_gaussReading_twoChartModel_x1_mul
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

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (O : Subring (AlgebraicClosure ℚ)) (hO : O ≤ Pl.toSubring)
    (ρO : A →+* ↥O) (hρO : O.subtype.comp ρO = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ) :

    ∀ (r₁ : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) → AlgebraicCurve.Place k ↥(ModularCurve.x1FunctionFieldC k M)),
      ModularCurve.IsLaurentPlaceReduction Pl πk (ModularCurve.x1FunctionField M) (ModularCurve.x1FunctionFieldC k M) r₁ →
      ModularCurve.LaurentPrincipalGeneratedByIntegral Pl πk (ModularCurve.x1FunctionField M) (ModularCurve.x1FunctionFieldC k M) →
      ∀ (ι : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar (M * p))) (hι : ι.toRingHom.IsIntegral)
        (ῑ : ↥(ModularCurve.x1FunctionFieldC k M) →ₐ[k] ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (hῑ : ῑ.toRingHom.IsIntegral),
        ModularCurve.QExpSemistable.IsQExpInclusion ι → ModularCurve.QExpSemistable.IsQExpInclusion ῑ →
        ∀ (D₁ : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M))))
          (Dη : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.x1FunctionFieldBar (M * p)))),
          ModularCurve.QExpSemistable.IsConormAlong ι hι
            (D₁ : Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M))) (Dη : Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p))) →

          ∀ (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) D.toBase),
            (gpts (Pic0.mk Dη)).1 = Spec.map (CommRingCat.ofHom O.subtype) ≫ z.1 →

            ∀ (y : G.J0s),
              (pts y).1 ≫ pullback.fst D.toBase (specMap A k) =
                Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ z.1 →
              ∀ (Dbar : Divisor.degZero (K := k) (F := ↥(ModularCurve.igusaFunctionFieldX1C k M w))),
                ModularCurve.QExpSemistable.IsConormAlong ῑ hῑ
                  (Finsupp.mapDomain r₁ (D₁ : Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)))) (Dbar : Divisor k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) →
                θ₁ (G.proj y).1 = Pic0.mk Dbar := by sorry
