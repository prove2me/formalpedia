-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_points_fixedValuationSubring_of_smul_eq_self_of_mem_normFreePart_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_points_fixedValuationSubring_of_smul_eq_self_of_mem_normFreePart_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/55a9b305-052e-57b9-a1d6-590bad7907ae
-- title:
--   Inertia-fixed norm-free classes extend over the invariant subring
-- statement:
--   Fix a prime $p$ and $M\ge 5$ with $p\nmid M$; let $L$ be a field of characteristic zero that is a $p$-cyclotomic extension of $\mathbb Q$, $\zeta\in L$ a primitive $p$-th root of unity, and let $K$ be the $L$-subfield of $\operatorname{LaurentSeries} L$ obtained by adjoining to $L$ the coefficientwise images of the function field [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137) of $X_1(Mp)$ over $\mathbb Q$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in its maximal ideal and $\zeta$ lies in the image of $A$, with $K$ an $A$-algebra compatibly, and let $j\in K$ be the element whose Laurent expansion is the coefficientwise image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), with $j\neq 0$. Let [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) be the associated two-chart model over $\operatorname{Spec}A$, $\varepsilon$ a section of it over the identity of $\operatorname{Spec}A$, and $D$ a relative $\mathrm{Pic}^0$ designation for that model, i.e. a scheme $D.P$ with structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec}A$ and a zero section, assumed (via a nonempty `RepresentsRelSubPic`) to represent the functor of rigidified line bundles that are fibrewise algebraically equivalent to zero, and assumed smooth and separated over $\operatorname{Spec}A$. Further data are fixed: embeddings of $A$ and $L$ into $\overline{\mathbb Q}$ forming a scalar tower; the hypotheses [`ModularCurve.HeckeDiamondInputsAll (M * p)`](def/ModularCurve_X1HeckeModule.html#L58) and [`ModularCurve.HeckeDiamondCommuteBar (M * p)`](def/ModularCurve_X1HeckeModule.html#L54) that supply and make commute the Hecke and diamond generators on $J_1(Mp)=$ [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186); a semiring action of $\operatorname{Gal}(L/\mathbb Q)$ on $A$ compatible with $A\to L$; a bijection $\mathrm{gpts}$ from $J_1(Mp)$ onto the $\overline{\mathbb Q}$-points of $D$ over $A$; endomorphisms $\varphi(t)$ of $D$ over $\operatorname{Spec}A$ indexed by $t$ in [`ModularCurve.HeckeAlgOne`](def/ModularCurve_X1HeckeModule.html#L16); and semilinear automorphisms $\tau(s)$ of $D.P$ over the twist of $D.\mathrm{toBase}$ by $s\in\operatorname{Gal}(L/\mathbb Q)$. These are required to be compatible in the following ways: each $\varphi(t)$ is additive for the relative group law coming from the representability hypothesis, $\mathrm{gpts}$ is additive and intertwines the Hecke module structure [`ModularCurve.heckeModuleOneBar (M * p)`](def/ModularCurve_X1HeckeModule.html#L129) with composition by $\varphi(t)$, $\tau(1)$ is the identity, $\tau(ss')$ is $\tau(s)$ followed by $\tau(s')$, each $\tau(s)$ commutes with each $\varphi(t)$, and for $\sigma'\in\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ restricting to $s$ on $L$ one has $\mathrm{gpts}(\sigma'\cdot x)=\operatorname{Spec}(\sigma')$ followed by $\mathrm{gpts}(x)$ followed by $\tau(s^{-1})$. Let $Pl$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ in its nonunits and $\rho:A\to Pl$ a factorisation of $A\to\overline{\mathbb Q}$. Finally let $a:\mathcal A\to\operatorname{Spec}A$ and $\iota:\mathcal A\to D.P$ over $\operatorname{Spec}A$ with $\iota$ a closed immersion, $a$ proper and smooth with connected fibres over every algebraically closed field, $\mathcal A$ closed under the identity, multiplication and inversion of the relative group law of $D$ through $\iota$, stable under every $\varphi(t)$, and such that a class $x\in J_1(Mp)$ lies in the norm-free part [`ModularCurve.normFreePartAt (M * p) p`](def/ModularCurve_X1PrimitiveSpecializationAtP.html#L29) exactly when $\mathrm{gpts}(x)$ factors through $\iota$ on $\overline{\mathbb Q}$-points. The conclusion: for every subgroup $I$ of $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ contained in the inertia subgroup of $Pl$ over $\mathbb Q$ and fixing every $p$-th root of unity in $\overline{\mathbb Q}$, every ring homomorphism $\rho_I$ from $A$ to $Pl\cap\overline{\mathbb Q}^{\,I}$ lifting $A\to\overline{\mathbb Q}$, and every $y$ in the norm-free part with $\sigma\cdot y=y$ for all $\sigma\in I$, there is a point $z$ of $D.P$ over $\operatorname{Spec}(\rho_I)$ such that $\mathrm{gpts}(y)$ is the map induced by the inclusion $Pl\cap\overline{\mathbb Q}^{\,I}\hookrightarrow\overline{\mathbb Q}$ followed by $z$.
--
--   This is the integrality-and-descent step for the norm-free part of $J_1(Mp)$: an inertia-invariant norm-free class, viewed as a $\overline{\mathbb Q}$-point of the relative $\mathrm{Pic}^0$ scheme, is shown to come from a point over the subring $Pl\cap\overline{\mathbb Q}^{\,I}$ of invariants, using that the class lands in the proper smooth subgroup scheme $\mathcal A$. It is used in the subsequent study of the norm-free family, in particular for its Hecke pairings and for membership results for inertia-fixed classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_points_fixedValuationSubring_of_smul_eq_self_of_mem_normFreePart_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.XOneP.exists_points_fixedValuationSubring_of_smul_eq_self_of_mem_normFreePart_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)
    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]
    (hin : ModularCurve.HeckeDiamondInputsAll (M * p)) (hcomm : ModularCurve.HeckeDiamondCommuteBar (M * p))

    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a))

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

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))

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
          NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp x ι) (φ t)) :
    ∀ (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : I ≤ Pl.inertiaSubgroupIn ℚ)
      (hIμ : ∀ σ ∈ I, ∀ ζ' : AlgebraicClosure ℚ, ζ' ^ p = 1 → σ ζ' = ζ')
      (ρI : A →+* ↥(Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring))
      (hρI : (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring).subtype.comp ρI =
        algebraMap A (AlgebraicClosure ℚ)),
      ∀ y ∈ ModularCurve.normFreePartAt (M * p) p, (∀ σ ∈ I, σ • y = y) →
        ∃ z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρI)) D.toBase,
          (gpts y).1 = Spec.map (CommRingCat.ofHom (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring).subtype) ≫ z.1 := by sorry
