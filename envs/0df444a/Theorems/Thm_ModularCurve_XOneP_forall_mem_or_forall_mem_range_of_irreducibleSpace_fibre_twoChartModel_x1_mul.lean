-- Prove2me | Theorems.Thm_ModularCurve_XOneP_forall_mem_or_forall_mem_range_of_irreducibleSpace_fibre_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.forall_mem_or_forall_mem_range_of_irreducibleSpace_fibre_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/8b31b122-f006-52c3-9efe-3fd203bd12ea
-- title:
--   Irreducible fibre pieces: u or u' vanishes identically
-- statement:
--   Fix a prime $p$ and a nonzero $M$ with $5 \le M$ and $p \nmid M$; let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$ and $\zeta \in L$ a primitive $p$-th root of unity. Let $K$ be the intermediate field of $L \subseteq \operatorname{LaurentSeries} L$ obtained by adjoining to $L$ the image, under the coefficientwise map induced by $\mathbb{Q} \to L$, of the function field of $X_1(Mp)$ inside $\operatorname{LaurentSeries}\mathbb{Q}$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A$, and let $K$ carry a compatible $A$-algebra structure. Let $j \in K$ be nonzero with Laurent expansion the coefficient embedding of the $q$-expansion $q^{-1}\cdot j_{\mathrm{num}}$, and let $u, u'$ lie in $\mathrm{chartAlgFin}\,A\,K\,j$, the $A$-subalgebra of elements of $K$ integral over $A[j]$, with $u u' = p^{12}$. Let $k$ be a field and $\varphi : A \to k$ a non-injective ring homomorphism, $C$ a scheme with irreducible underlying space, and $i$ a morphism from $C$ to the pullback of [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) along $\operatorname{Spec}\varphi$. Then either for every point $z$ in the range of $i$ on underlying spaces and every prime $\mathfrak{q}$ of $\mathrm{chartAlgFin}\,A\,K\,j$ whose image under `ιFin` is the image of $z$ under the first projection, one has $u \in \mathfrak{q}$; or the same holds with $u'$ in place of $u$.
--
--   This is the pointwise-to-global step for a pair of modular units with product $p^{12}$ on the fibre over the closed point of the two-chart model of $X_1(Mp)$: on an irreducible piece of that fibre, one of the two units vanishes along the whole piece. It feeds the dictionary for modular units on this model, [`ModularCurve.XOneP.modularUnit_dictionary_or_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.modularUnit_dictionary_or_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_forall_mem_or_forall_mem_range_of_irreducibleSpace_fibre_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian TensorProduct

theorem ModularCurve.XOneP.forall_mem_or_forall_mem_range_of_irreducibleSpace_fibre_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (u u' : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (huu' : u * u' = (p : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) ^ 12)
    (k : Type) [Field k] (φ : A →+* k) (hφ : ¬ Function.Injective φ)
    {C : Scheme.{0}} [IrreducibleSpace ↥C] (i : C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ))) :
    (∀ z ∈ Set.range i.base, ∀ 𝔮 : ↥(ModularCurve.TwoChart.XFin A (↥K) j),
        (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ))).base z = (ModularCurve.TwoChart.ιFin A (↥K) j).base 𝔮 → u ∈ 𝔮.asIdeal) ∨
    (∀ z ∈ Set.range i.base, ∀ 𝔮 : ↥(ModularCurve.TwoChart.XFin A (↥K) j),
        (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ))).base z = (ModularCurve.TwoChart.ιFin A (↥K) j).base 𝔮 → u' ∈ 𝔮.asIdeal) := by sorry
