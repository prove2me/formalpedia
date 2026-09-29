-- Prove2me | Theorems.Thm_ModularCurve_XOneP_forall_exists_orientedEtaleCrossingChart_valuationSubring_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.forall_exists_orientedEtaleCrossingChart_valuationSubring_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/5b51ba77-488e-5be2-8817-066467aaaf47
-- title:
--   Inertia-equivariant oriented étale crossing chart for X₁(Mp) over Pl
-- statement:
--   Fix a prime $p$ and $M\ge 5$ with $p\nmid M$; let $L$ be a characteristic-zero field which is a $p$-th cyclotomic extension of $\mathbb{Q}$, $\zeta\in L$ a primitive $p$-th root of unity, and $K\subseteq L((q))$ the intermediate field obtained by adjoining to $L$ the image of the function field $\mathrm{x1FunctionField}(Mp)$ of $X_1(Mp)$ over $\mathbb{Q}$ under the coefficientwise embedding $\mathrm{LaurentSeries}\,\mathbb{Q}\to\mathrm{LaurentSeries}\,L$. Let $A$ be a discrete valuation ring with fraction field $L$, with $p$ in its maximal ideal, with $\zeta$ in the image of $A$, and with $K$ an $A$-algebra compatibly with $L$; let $j\in K$ be nonzero with Laurent expansion the $q$-expansion $\mathrm{jq}$. Let $k$ be an algebraically closed $A$-algebra field of characteristic $p$, and let $C_1,C_2$ be proper, smooth of relative dimension $1$, geometrically integral $k$-schemes together with closed immersions $i_1,i_2$ over $k$ into the base change $\mathrm{pullback}(\mathrm{TwoChart.modelTo}\,A\,K\,j,\ \mathrm{Spec}\,k\to\mathrm{Spec}\,A)$, whose images cover that fibre; assume the scheme-theoretic intersection $C_1\times_{X_k}C_2$ is reduced with cardinality $n>0$, and let $\varpi$ generate the maximal ideal of $A$. Let $Pl$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit, $\rho:A\to Pl$ a ring map inducing the given map to $\overline{\mathbb{Q}}$, and $\pi_k:Pl\to k$ a surjection with $\pi_k\circ\rho$ the structure map $A\to k$; finally let $bc$ be a morphism from the $k$-fibre of the model to $X_{Pl}:=\mathrm{pullback}(\mathrm{modelTo}\,A\,K\,j,\ \mathrm{Spec}\,\rho)$ commuting with the first projections and with the second projections up to $\mathrm{Spec}\,\pi_k$. The conclusion is that for every point $\nu$ of $C_1\times_{X_k}C_2$, writing $x_\nu$ for its image in $X_{Pl}$ under $\mathrm{pullback.fst}$ followed by $i_1$ and $bc$, there are $e\ge 1$, an open $U\subseteq X_{Pl}$ with $x_\nu\in U$, and a morphism $f:U\to\mathrm{Spec}\,Pl[X_0,X_1]/(X_0X_1-\rho(\varpi)^e)$ such that: $f$ is a morphism over $\mathrm{Spec}\,Pl$, i.e. $f$ followed by $\mathrm{Spec}$ of the structure map $Pl\to\mathrm{CrossingQuotient}\,Pl\,(\rho\varpi)^e$ equals the inclusion $U\hookrightarrow X_{Pl}$ followed by the second projection; a point $y\in U$ has both $\mathrm{CrossingQuotient.U}((\rho\varpi)^e)$ and $\mathrm{CrossingQuotient.V}((\rho\varpi)^e)$ in the prime $f(y)$ exactly when $y$ maps to $x_\nu$; at every $y$ over $x_\nu$ the stalk map of $f$ is flat, sends the maximal ideal onto the maximal ideal, and induces an isomorphism of residue fields; there is an open $W\subseteq U$ containing some point over $x_\nu$ with $W\hookrightarrow U$ followed by $f$ étale; $f$ is equivariant for inertia over $L$, in the sense that for $\tau$ in the decomposition subgroup of $Pl$ over $\mathbb{Q}$ lying in the inertia subgroup and acting trivially on the image of $L$, for $x',y'\in Pl$ with $x'y'=(\rho\varpi)^e$ and $\tau(x')\tau(y')=(\rho\varpi)^e$, and for $Pl$-sections $s,s'$ of $U$ over $\mathrm{Spec}\,Pl$ satisfying $s'$ followed by $U\hookrightarrow X_{Pl}$ and the first projection $=\mathrm{Spec}\,\tau$ followed by the same composite for $s$, if $s$ followed by $f$ is $\mathrm{Spec}$ of the $Pl$-algebra map sending the two coordinates to $x',y'$ then $s'$ followed by $f$ is $\mathrm{Spec}$ of the map sending them to $\tau(x'),\tau(y')$; and $f$ is oriented, in that for $y\in U$ one has $\mathrm{CrossingQuotient.V}((\rho\varpi)^e)\in f(y)$ if and only if $y$ lies over the image of $i_1$ composed with $bc$, and $\mathrm{CrossingQuotient.U}((\rho\varpi)^e)\in f(y)$ if and only if $y$ lies over the image of $i_2$ composed with $bc$.
--
--   This is the étale-local description of the two-chart model of $X_1(Mp)$ at a crossing of its geometric special fibre: near each such point the model is, étale-locally over the valuation ring $Pl\subset\overline{\mathbb{Q}}$, the ordinary double point $uv=\rho(\varpi)^e$, with the two branches $u=0$ and $v=0$ matched to the two components $C_2$ and $C_1$ and with the chart compatible with the action of the inertia group over $\mathbb{Q}(\zeta_p)$. It is the version over the place itself, obtained from the chart over an unramified base by base change, and it feeds the construction of the tube bijection and of the gluing data for the line bundle on the annulus used in the analysis of the component group and of the reduction of the Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_forall_exists_orientedEtaleCrossingChart_valuationSubring_twoChartModel_x1_mul.lean

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
import Definitions.Def_MvPolynomial_CrossingResolutionScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPolynomial CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.forall_exists_orientedEtaleCrossingChart_valuationSubring_twoChartModel_x1_mul
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
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ) (hπk : Function.Surjective πk)

    (bc : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom πk)) :
    ∀ ν : ↥(pullback i₁.1 i₂.1),
      ∃ (e : ℕ) (_ : 1 ≤ e)
        (U : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ))).Opens)
        (_ : (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bc).base ν ∈ U)
        (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme ((ρ ϖ) ^ e)),

        f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥Pl (CrossingQuotient ↥Pl ((ρ ϖ) ^ e)))) =
            U.ι ≫ pullback.snd _ _ ∧

        (∀ y : ↥(U : Scheme.{0}),
            (CrossingQuotient.U ((ρ ϖ) ^ e) ∈ (f.base y).asIdeal ∧
              CrossingQuotient.V ((ρ ϖ) ^ e) ∈ (f.base y).asIdeal) ↔
            U.ι.base y = (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bc).base ν) ∧

        (∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bc).base ν →
            (f.stalkMap y).hom.Flat ∧
            Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
            IsIso (f.residueFieldMap y)) ∧

        (∃ W : (U : Scheme.{0}).Opens,
          (∃ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bc).base ν ∧ y ∈ W) ∧
          AlgebraicGeometry.Etale (W.ι ≫ f)) ∧

        (∀ (τ : ↥(Pl.decompositionSubgroup ℚ)), τ ∈ Pl.inertiaSubgroup ℚ →
          (∀ l : L, (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
          ∀ (x' y' : ↥Pl) (hxy : x' * y' = algebraMap ↥Pl ↥Pl ((ρ ϖ) ^ e))
            (hxy' : (MulSemiringAction.toRingHom _ (↥Pl) τ) x' * (MulSemiringAction.toRingHom _ (↥Pl) τ) y' =
              algebraMap ↥Pl ↥Pl ((ρ ϖ) ^ e))
            (sU sU' : Spec (CommRingCat.of ↥Pl) ⟶ (U : Scheme.{0})),
            sU ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ → sU' ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ →
            sU' ≫ U.ι ≫ pullback.fst _ _ =
              Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom _ (↥Pl) τ)) ≫ sU ≫ U.ι ≫ pullback.fst _ _ →
            sU ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := (ρ ϖ) ^ e) x' y' hxy).toRingHom) →
            sU' ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := (ρ ϖ) ^ e)
              ((MulSemiringAction.toRingHom _ (↥Pl) τ) x') ((MulSemiringAction.toRingHom _ (↥Pl) τ) y') hxy').toRingHom)) ∧

        (∀ y : ↥(U : Scheme.{0}), CrossingQuotient.V ((ρ ϖ) ^ e) ∈ (f.base y).asIdeal →
            U.ι.base y ∈ Set.range (i₁.1 ≫ bc).base) ∧
        (∀ y : ↥(U : Scheme.{0}), CrossingQuotient.U ((ρ ϖ) ^ e) ∈ (f.base y).asIdeal →
            U.ι.base y ∈ Set.range (i₂.1 ≫ bc).base) ∧

        (∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (i₁.1 ≫ bc).base →
            CrossingQuotient.V ((ρ ϖ) ^ e) ∈ (f.base y).asIdeal) ∧
        (∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (i₂.1 ≫ bc).base →
            CrossingQuotient.U ((ρ ϖ) ^ e) ∈ (f.base y).asIdeal) := by sorry
