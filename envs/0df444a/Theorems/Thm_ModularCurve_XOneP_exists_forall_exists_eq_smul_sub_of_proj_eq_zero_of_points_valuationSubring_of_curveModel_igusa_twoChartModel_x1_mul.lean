-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_forall_exists_eq_smul_sub_of_proj_eq_zero_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_forall_exists_eq_smul_sub_of_proj_eq_zero_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/7ba0c345-a103-5fae-940f-10a45fdebfb7
-- title:
--   Toric prime-to-p torsion classes of J₁(Mp) are γ· w-w
-- statement:
--   Fix a prime $p$ and an integer $M$ with $5\le M$ and $p\nmid M$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, and let $\zeta\in L$ be a primitive $p$-th root of unity. Let $K$ be an intermediate field of $L\subseteq\operatorname{LaurentSeries}L$ with $K=\mathtt{laurentBaseChange}\,L\,(\mathtt{x1FunctionField}\,(Mp))$, that is, $K$ is generated over $L$ by the coefficientwise images of the function field of $X_1(Mp)$ inside $L((q))$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A\to L$, with $K$ an $A$-algebra compatibly with $A\to L\to K$. Let $j\in K$ be nonzero with Laurent expansion the image under $\mathtt{coeffEmb}\,L$ of the $q$-expansion $\mathtt{jq}$ of the modular function $j$; the associated two-chart model of $X_1(Mp)$ over $A$ has structure morphism $\mathtt{modelTo}\,A\,K\,j$, obtained by gluing the spectra of the subalgebras $\mathtt{chartAlgFin}$ and $\mathtt{chartAlgInf}$ of $K$ over $A$, and this morphism is assumed proper.
--
--   Special fibre data. Let $k$ be an algebraically closed $A$-algebra field of characteristic $p$, and let $c_1:C_1\to\operatorname{Spec}k$, $c_2:C_2\to\operatorname{Spec}k$ be proper, smooth of relative dimension $1$ and geometrically integral. Let $i_1,i_2$ be closed immersions of $C_1$, $C_2$ into the base change $\mathtt{baseChange}\,A\,(\mathtt{modelTo}\,A\,K\,j)\,k$ over $k$. The hypothesis `hcover` states that every point of the pullback of the two-chart model along $\operatorname{Spec}k\to\operatorname{Spec}A$ lies in the image of $i_1$ or of $i_2$; `hred` states that the scheme-theoretic intersection $\mathtt{pullback}\,i_1\,i_2$ is reduced, and `hn`, `hn0` name its cardinality $n>0$.
--
--   Sections. Let $\varepsilon$ be a section of $\mathtt{modelTo}\,A\,K\,j$ over $\operatorname{Spec}A$, and $\varepsilon_1,\varepsilon_2$ sections of $c_1,c_2$; `hε₁` requires $\varepsilon_1$ followed by $i_1$ to be the base change of $\varepsilon$ to $k$.
--
--   Relative $\operatorname{Pic}^0$ data. Let $D$ be a $\mathtt{RelativePic0Designation}$ for $\mathtt{modelTo}\,A\,K\,j$, i.e. a scheme $D.P$ with a morphism $D.\mathtt{toBase}$ to $\operatorname{Spec}A$ and a zero section; `hrep` asserts that $D$ represents, with rigidification along $\varepsilon$, the sub-Picard condition $\mathtt{algEquivZeroCut}$ (whose predicate on a rigidified line bundle is $\mathtt{FibrewiseAlgEquivZero}$): there is a rigidified Poincaré bundle on the curve over $D.\mathtt{toBase}$ satisfying the condition, every rigidified line bundle satisfying it over a base $T$ is induced by a unique section of $D.\mathtt{toBase}$ over $T$, and the pullback along the zero section is trivial. Further, $D.\mathtt{toBase}$ is smooth (`hsm`) and separated (`hsep`). The hypothesis `hreps` is the same representability statement over $k$ for the base-changed curve, the base-changed section of $\varepsilon$ and the designation $D.\mathtt{baseChange}\,k$, and `hPk` says its Poincaré bundle is isomorphic to the base change, in the sense of $\mathtt{BaseChange.ofR}$, of the pullback of the Poincaré bundle of `hrep` along the first projection of $D.\mathtt{toBase}\times_{\operatorname{Spec}A}\operatorname{Spec}k$. Designations $D_1,D_2$ over $k$ with representability data `hrep₁`, `hrep₂` are given for $c_1,c_2$ with the sections $\varepsilon_1,\varepsilon_2$.
--
--   Comparison of the component Jacobians. Let $\nu_2$ be a morphism from $(D.\mathtt{baseChange}\,k).\mathtt{toBase}$ to $D_2.\mathtt{toBase}$ over $\operatorname{Spec}k$ such that (`hν₂`) for every $k$-scheme $t:T\to\operatorname{Spec}k$ and every section $a$ of $(D.\mathtt{baseChange}\,k).\mathtt{toBase}$ over $T$, the pullback of the Poincaré bundle of `hrep₂` along $a$ followed by $\nu_2$ is isomorphic to the $\mathtt{rigidify}$, along the section $\mathtt{rigSection}\,c_2\,t\,\varepsilon_2$ and the projection $\mathtt{pullback.snd}\,c_2\,t$, of the pullback along $\mathtt{curveChange}\,i_2$ of the bundle obtained from `hreps` at $a$.
--
--   Generic geometric model. Assume compatible $\mathbb{Q}$-algebra structures $A\to\overline{\mathbb{Q}}$ and $L\to\overline{\mathbb{Q}}$. Let $M_\eta$ be a $\mathtt{CurveModel}$ over $\overline{\mathbb{Q}}$ of $\mathtt{x1FunctionFieldBar}\,(Mp)$ — a proper smooth integral curve together with an isomorphism of its function field with that field, a bijection between its closed points and the places, compatibility of stalk images with valuation subrings, and the property that finite sets of points lie in an affine open — and let $e_\eta$ be an isomorphism from $M_\eta.C$ to the pullback of the two-chart model along $\operatorname{Spec}\overline{\mathbb{Q}}\to\operatorname{Spec}A$, compatible with the structure morphisms (`heη`). The preimage under $e_\eta$ followed by the first projection of the image of the finite chart is assumed nonempty, and the pinning hypothesis `hMηpin` requires, for every element $a$ of $\mathtt{chartAlgFin}\,A\,K\,j$, that the element of $\mathtt{x1FunctionFieldBar}\,(Mp)$ corresponding under $M_\eta.\mathtt{ffEquiv}^{-1}$ to the germ at the generic point of the function induced by $a$ have Laurent expansion the coefficientwise image under $L\to\overline{\mathbb{Q}}$ of the Laurent expansion of $a$. The hypothesis `hgal` requires that for every $g\in\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ fixing the image of $L$ pointwise and all $\overline{\mathbb{Q}}$-points $x,x'$ of $M_\eta.C$: if $x'$ followed by $e_\eta$ and the first projection equals $\operatorname{Spec}(g)$ followed by $x$, $e_\eta$ and the first projection, then $M_\eta.\mathtt{pointEquivPlace}\,x'$ is the image of $M_\eta.\mathtt{pointEquivPlace}\,x$ under the action of $\mathtt{arithmeticGalois}\,(\mathtt{x1FunctionField}\,(Mp))\,g$ on places.
--
--   Special fibre group data. Let $G$ be a $\mathtt{NeronSpecialFibreGeom}\,p$: abelian groups $G.\mathtt{J0s}$, $G.\mathtt{JI}$, $G.\mathtt{JE}$, a subgroup $G.\mathtt{torus}\subseteq G.\mathtt{J0s}$ and a surjective homomorphism $G.\mathtt{proj}:G.\mathtt{J0s}\to G.\mathtt{JI}\times G.\mathtt{JE}$ with kernel $G.\mathtt{torus}$. Bijections $\mathtt{pts}$, $\mathtt{ptsI}$, $\mathtt{ptsE}$ identify $G.\mathtt{J0s}$, $G.\mathtt{JI}$, $G.\mathtt{JE}$ with the $k$-points of $(D.\mathtt{baseChange}\,k).\mathtt{toBase}$, $D_1.\mathtt{toBase}$, $D_2.\mathtt{toBase}$ respectively; the hypotheses `hadd`, `haddI`, `haddE` state that each of the three bijections is additive in the sense that the Poincaré bundle pulled back at a sum is isomorphic to the tensor product of the pullbacks at the summands, and `hproj` states that for every $x\in G.\mathtt{J0s}$ the point $\mathtt{ptsI}((G.\mathtt{proj}\,x)_1)$ is $\mathtt{pts}\,x$ followed by the classifying morphism $\mathtt{RepresentsRelSubPic.pullbackHom}$ attached to $i_1$, and $\mathtt{ptsE}((G.\mathtt{proj}\,x)_2)$ is $\mathtt{pts}\,x$ followed by $\nu_2$.
--
--   Igusa models of the two components. Let $w$ be an $\mathtt{IntegralWeightOneForm}\,k\,M$, that is a weight-one modular form on $\Gamma_1(M)$ together with an integral $q$-expansion whose reduction over $k$ is nonzero, and let $\mathtt{Mdl}_1,\mathtt{Mdl}_2$ be curve models over $k$ of the Igusa function field $\mathtt{igusaFunctionFieldX1C}\,k\,M\,w$, with isomorphisms $e_1:\mathtt{Mdl}_1.C\cong C_1$ and $e_2:\mathtt{Mdl}_2.C\cong C_2$ over $k$ (`he₁`, `he₂`).
--
--   Abel–Jacobi pinning of the generic dictionary. Let $\mathtt{gpts}$ be a bijection from $\mathtt{JOne}\,(Mp)=\operatorname{Pic}^0(\overline{\mathbb{Q}},\mathtt{x1FunctionFieldBar}\,(Mp))$ — degree-zero divisors modulo principal ones — onto the sections of $D.\mathtt{toBase}$ over $\operatorname{Spec}\overline{\mathbb{Q}}\to\operatorname{Spec}A$, which is additive for the relative group law of `hrep` attached to $\mathtt{algEquivZeroGroupCut}$ (`hgadd`). The hypothesis `hDL` is representability over $L$ for the base-changed curve and designation, `hPL` the corresponding base-change comparison of Poincaré bundles, $\mathtt{ajL}$ a morphism from the base-changed curve over $L$ to $(D.\mathtt{baseChange}\,L).\mathtt{toBase}$ with $\varepsilon$ mapped to the zero section (`hajLε`) and with the Abel–Jacobi property `hajL`: for every field $K'$, every $t:\operatorname{Spec}K'\to\operatorname{Spec}L$ and every $K'$-point $x$ of the curve, the pullback of the Poincaré bundle along $x$ followed by $\mathtt{ajL}$ is isomorphic to the line bundle of the relative effective Cartier divisor of the point $x$ tensored with the ideal module of the divisor of the section $\varepsilon$, i.e. to $\mathcal{O}(x-\varepsilon)$. Further, $\mathtt{kL}$ is a morphism from the pullback of the two-chart model over $\overline{\mathbb{Q}}$ to the one over $L$ compatible with both projections (`hkL₁`, `hkL₂`); $\mathtt{ajbar}:M_\eta.C\to D.P$ is defined by `hajbar` as $e_\eta$ followed by $\mathtt{kL}$, $\mathtt{ajL}$ and the first projection, and lies over $\operatorname{Spec}\overline{\mathbb{Q}}\to\operatorname{Spec}A$ (`hajbar_over`); $\bar\varepsilon$ is a $\overline{\mathbb{Q}}$-point of $M_\eta.C$ inducing $\varepsilon$ (`hεbar`) and sent by $\mathtt{ajbar}$ to the zero section (`hεbar_aj`). Finally `hpts_aj` requires: for all $\overline{\mathbb{Q}}$-points $x,s$ of $M_\eta.C$ with $s$ inducing $\varepsilon$, there is a degree-zero divisor $D_v$ on $\mathtt{x1FunctionFieldBar}\,(Mp)$ equal to the difference of the places of $x$ and of $s$, each with multiplicity one, whose class satisfies $\mathtt{gpts}(\,[D_v]\,)=x$ followed by $\mathtt{ajbar}$.
--
--   Reduction data. Let $\mathrm{Pl}$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $\mathrm{Pl}$ (`hPl`), let $\rho:A\to\mathrm{Pl}$ be a ring homomorphism inducing $A\to\overline{\mathbb{Q}}$ (`hρ`), and let $\pi_k:\mathrm{Pl}\to k$ be a surjective ring homomorphism with $\pi_k\circ\rho$ the structure map $A\to k$.
--
--   Conclusion. There exist a natural number $e$ with $0<e$ and $e$ coprime to $p$, and an automorphism $\gamma$ of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ lying in $\mathrm{Pl}.\mathtt{inertiaSubgroupIn}\,\mathbb{Q}$ (the image in $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $\mathrm{Pl}$ inside its decomposition subgroup) and fixing the image of $L$ in $\overline{\mathbb{Q}}$ pointwise, with the following property. For every natural number $m$ with $0<m$ and $m$ coprime to $p$, every $x\in\mathtt{JOne}\,(Mp)$ with $m\cdot x=0$, every $\mathrm{Pl}$-point $z$ of $D.P$ over $\operatorname{Spec}(\rho)$, and every $y\in G.\mathtt{J0s}$: if the section $\mathtt{gpts}\,x$ is the restriction of $z$ along $\mathrm{Pl}\hookrightarrow\overline{\mathbb{Q}}$, if the $k$-point of $D.P$ obtained from $\mathtt{pts}\,y$ by the first projection of $D.\mathtt{toBase}\times_{\operatorname{Spec}A}\operatorname{Spec}k$ is the reduction of $z$ along $\pi_k$, and if $G.\mathtt{proj}\,y=0$ (equivalently $y\in G.\mathtt{torus}$), then there exists a class $w_0\in\mathtt{JOne}\,(Mp)$ (the Lean binder reuses the name `w` of the weight-one form) such that $(me)\cdot w_0=0$ and $x=\gamma\cdot w_0-w_0$, the action being the natural one of $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $\mathtt{JOne}\,(Mp)$.
--
--   This is the finite-level, prime-to-$p$ form of Grothendieck's monodromy description of the toric part of the Néron model of $J_1(Mp)$ at $p$: classes that reduce into the kernel of the projection to the Jacobians of the two Igusa components are of the form $\gamma\cdot w-w$ for a single inertia element $\gamma$ fixing $\mathbb{Q}(\zeta_p)$, after a bounded prime-to-$p$ shift $e$ of the torsion order. It feeds the orthogonality computation [`ModularCurve.XOneP.weilDatum_pairing_eq_one_of_proj_eq_zero_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.weilDatum_pairing_eq_one_of_proj_eq_zero_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul) for the Weil pairing on the toric part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_forall_exists_eq_smul_sub_of_proj_eq_zero_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul.lean

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

theorem ModularCurve.XOneP.exists_forall_exists_eq_smul_sub_of_proj_eq_zero_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul
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
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ) (hπk : Function.Surjective πk) :
    ∃ e : ℕ, 0 < e ∧ e.Coprime p ∧
    ∃ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, γ ∈ Pl.inertiaSubgroupIn ℚ ∧
      (∀ l : L, γ (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) ∧
      ∀ (m : ℕ), 0 < m → m.Coprime p →
        ∀ (x : ModularCurve.JOne (M * p)), m • x = 0 →
          ∀ (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y : G.J0s),
            (gpts x).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z.1 →
            (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z.1 →
            G.proj y = 0 →
              ∃ w : ModularCurve.JOne (M * p), (m * e) • w = 0 ∧ x = γ • w - w := by sorry
