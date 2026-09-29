-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_reduction_torsion_bijective_points_fixedValuationSubring_of_representsRelSubPic_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_reduction_torsion_bijective_points_fixedValuationSubring_of_representsRelSubPic_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/5007b403-320d-599e-a0c9-0c8a8defd117
-- title:
--   Reduction bijective on prime-to-p torsion of O_I-points
-- statement:
--   Fix a prime $p$, an integer $M\ge 5$ with $p\nmid M$, a field $L$ of characteristic zero which is a $p$-th cyclotomic extension of $\mathbb{Q}$ with primitive $p$-th root of unity $\zeta$, and $K$ the intermediate field of $L\subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the coefficientwise image of the function field of $X_1(Mp)$. Let $A$ be a discrete valuation domain with fraction field $L$, with $p$ in its maximal ideal and $\zeta$ in the image of $A$, acting compatibly on $K$, and let $j\in K$ be nonzero with Laurent expansion the coefficientwise image of the $q$-expansion $\mathtt{jq}$. Let $\varepsilon$ be an $A$-section of the structure morphism $\mathtt{modelTo}$ of the two-chart model of $K$ over $A$, and let $D$ consist of a scheme $D.P$, a morphism $D.\mathtt{toBase}$ to $\operatorname{Spec} A$ which is smooth and separated, and a zero section splitting it; assume a witness that $D$ represents the functor of $\varepsilon$-rigidified line bundles on the two-chart model whose geometric fibres are algebraically equivalent to zero, so that $D$ carries the associated relative group law. Assume $\overline{\mathbb{Q}}$ is an algebra over $A$ and over $L$ compatibly, the Hecke–diamond input predicates $\mathtt{HeckeDiamondInputsAll}$ and $\mathtt{HeckeDiamondCommuteBar}$ at level $Mp$, and a semiring action of $\mathrm{Gal}(L/\mathbb{Q})$ on $A$ compatible with $A\to L$. Assume further a bijection $\mathtt{gpts}$ from $J_1(Mp)=\mathrm{Pic}^0$ of the $\overline{\mathbb{Q}}$-base-changed function field of $X_1(Mp)$ onto the $\overline{\mathbb{Q}}$-points of $D.\mathtt{toBase}$, endomorphisms $\varphi_t$ of $D.\mathtt{toBase}$ indexed by the Hecke algebra $\mathtt{HeckeAlgOne}=\mathrm{MvPolynomial}(\mathrm{Primes}\oplus\mathbb{N},\mathbb{Z})$ and semilinear transports $\tau_s$ indexed by $s\in\mathrm{Gal}(L/\mathbb{Q})$, subject to: each $\varphi_t$ respects the relative group law on $T$-points; $\mathtt{gpts}$ is equivariant for the Hecke module structure $\mathtt{heckeModuleOneBar}$ and additive for the relative group law; $\tau_1$ is the identity, $\tau_{ss'}=\tau_{s}$ followed by $\tau_{s'}$, each $\tau_s$ commutes with each $\varphi_t$; and, for $\sigma'\in\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ restricting to $s$ on $L$, $\mathtt{gpts}(\sigma'\cdot x)$ equals $\operatorname{Spec}\sigma'$ followed by $\mathtt{gpts}(x)$ followed by $\tau_{s^{-1}}$. Finally let $Pl$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit, let $\rho:A\to Pl$ factor $A\to\overline{\mathbb{Q}}$, and let $I$ be a subgroup of the inertia subgroup of $Pl$ over $\mathbb{Q}$ which fixes every $p$-th root of unity in $\overline{\mathbb{Q}}$ and has finite index in that inertia subgroup. Writing $O_I=Pl\cap \overline{\mathbb{Q}}^{\,I}$, the conclusion asserts the existence of a ring homomorphism $\rho_I:A\to O_I$ factoring $A\to\overline{\mathbb{Q}}$ such that, with $\mathtt{to\kappa}:O_I\to$ residue field of $Pl$ the residue map on $O_I\subseteq Pl$, with $D(O_I)$ and $D(\kappa)$ the points of $D.\mathtt{toBase}$ over $\rho_I$ and over $\mathtt{to\kappa}\circ\rho_I$, and with $\mathrm{dom}$ the set of $x\in J_1(Mp)$ for which $\mathtt{gpts}(x)$ is the base change along $O_I\hookrightarrow\overline{\mathbb{Q}}$ of some element of $D(O_I)$: (i) every $x\in\mathrm{dom}$ is fixed by every $\sigma\in I$; (ii) base change along $O_I\hookrightarrow\overline{\mathbb{Q}}$ is injective on $D(O_I)$; (iii) $0\in\mathrm{dom}$ and $\mathrm{dom}$ is closed under differences; (iv) for the group structures on $D(O_I)$ and $D(\kappa)$ coming from the relative group law, and for every $n>0$ with $p\nmid n$, reduction along $\mathtt{to\kappa}$ is injective on the $n$-torsion of $D(O_I)$ and every $n$-torsion point of $D(\kappa)$ lifts to an $n$-torsion point of $D(O_I)$; (v) for every $\varphi'\in\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ which is a Frobenius at $p$ for $Pl$ (lying in the decomposition group and acting as the $p$-th power map on the residue field) and which normalises $I$, the set $\mathrm{dom}$ is stable under $\varphi'$.
--
--   This is the specialisation statement for $\mathrm{Pic}^0$ of the stable model of $X_1(Mp)$ read on points with values in the inertia-fixed valuation rings $O_I=Pl\cap\overline{\mathbb{Q}}^{\,I}$: these rings are Henselian with algebraically closed residue field, so prime-to-$p$ torsion reduces bijectively, and the subgroup $\mathrm{dom}$ of $J_1(Mp)$ of points extending over $O_I$ is $I$-fixed and Frobenius-stable. It supplies the carrier for the pinned specialisation family used in the good-reduction analysis of $J_1(Mp)$, and is cited by [`ModularCurve.exists_qExpSemistableSpecializationPinnedV3_family_normFreePart_and_diamond_of_dvd_of_not_sq_dvd_of_le_div`](thm.html#ModularCurve.exists_qExpSemistableSpecializationPinnedV3_family_normFreePart_and_diamond_of_dvd_of_not_sq_dvd_of_le_div).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_reduction_torsion_bijective_points_fixedValuationSubring_of_representsRelSubPic_twoChartModel_x1_mul.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.XOneP.exists_reduction_torsion_bijective_points_fixedValuationSubring_of_representsRelSubPic_twoChartModel_x1_mul
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

    (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : I ≤ Pl.inertiaSubgroupIn ℚ)
    (hIμ : ∀ σ ∈ I, ∀ ζ' : AlgebraicClosure ℚ, ζ' ^ p = 1 → σ ζ' = ζ')
    (hIf : (I.subgroupOf (Pl.inertiaSubgroupIn ℚ)).FiniteIndex) :

    let OI : Subring (AlgebraicClosure ℚ) := Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring
    ∃ (ρI : A →+* ↥OI) (hρI : OI.subtype.comp ρI = algebraMap A (AlgebraicClosure ℚ)),

      let toκ : ↥OI →+* IsLocalRing.ResidueField ↥Pl := (IsLocalRing.residue ↥Pl).comp (Subring.inclusion inf_le_left)

      let DOI := SchemeHomOver (Spec.map (CommRingCat.ofHom ρI)) D.toBase
      let Dκ := SchemeHomOver (Spec.map (CommRingCat.ofHom (toκ.comp ρI))) D.toBase

      let dom : Set (ModularCurve.JOne (M * p)) :=
        {x | ∃ z : DOI, (gpts x).1 = Spec.map (CommRingCat.ofHom OI.subtype) ≫ z.1}

      (∀ x ∈ dom, ∀ σ ∈ I, σ • x = x) ∧

      (∀ z z' : DOI, Spec.map (CommRingCat.ofHom OI.subtype) ≫ z.1 = Spec.map (CommRingCat.ofHom OI.subtype) ≫ z'.1 → z = z') ∧

      (0 ∈ dom ∧ ∀ x ∈ dom, ∀ y ∈ dom, x - y ∈ dom) ∧

      (letI := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).pointGroup
          (Spec.map (CommRingCat.ofHom ρI))
       letI := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).pointGroup
          (Spec.map (CommRingCat.ofHom (toκ.comp ρI)))
       ∀ n : ℕ, 0 < n → ¬ p ∣ n →
         (∀ z : DOI, z ^ n = 1 → Spec.map (CommRingCat.ofHom toκ) ≫ z.1 = (1 : Dκ).1 → z = 1) ∧
         (∀ w : Dκ, w ^ n = 1 → ∃ z : DOI, z ^ n = 1 ∧ w.1 = Spec.map (CommRingCat.ofHom toκ) ≫ z.1)) ∧

      (∀ φ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, Pl.IsFrobeniusAt φ' p →
        (∀ σ, σ ∈ I ↔ φ' * σ * φ'⁻¹ ∈ I) → ∀ x ∈ dom, φ' • x ∈ dom) := by sorry
