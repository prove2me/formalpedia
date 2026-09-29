-- Prove2me | Theorems.Thm_ModularCurve_XOneP_nonempty_iso_unit_fibre_of_isAlgEquivZero_of_ne_zero_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.nonempty_iso_unit_fibre_of_isAlgEquivZero_of_ne_zero_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/6ff63b4b-7200-5be8-ac44-7db5464c0a75
-- title:
--   Triviality of sectioned algebraically trivial bundles on fibres of X₁(Mp)
-- statement:
--   Let $p$ be a prime and $M$ a non-zero natural number with $5 \le M$ and $p \nmid M$; let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, and $\zeta \in L$ a primitive $p$-th root of unity. Let $K$ be an intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), that is, the subfield generated over $L$ by the image of the function field $X_1(Mp)$-field of $\mathbb{Q}$-Laurent series under coefficientwise extension of scalars. Let $A$ be a discrete valuation domain with $L$ as fraction field, such that $p$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A \to L$, and let $K$ be an $A$-algebra compatibly with $A \to L \to K$. Let $j \in K$ be non-zero with underlying Laurent series [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81), the $q$-expansion of the $j$-invariant. Write $f =$ [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) for the structure morphism of the two-chart model over $\operatorname{Spec} A$, glued from the spectra of the finite and infinite chart algebras attached to $j$. The assertion is: for every algebraically closed field $k$, every morphism $x : \operatorname{Spec} k \to \operatorname{Spec} A$, and every module $\mathcal{L}$ on the fibre $P = \operatorname{pullback} f\,x$ which is invertible (every point of $P$ has an open neighbourhood $U$ on which the restriction of $\mathcal{L}$ is isomorphic to the unit module of $U$) and satisfies `IsAlgEquivZero (pullback.snd f x)` $\mathcal{L}$ — i.e. there are a scheme $T'$ and a morphism $h : T' \to \operatorname{Spec} k$ that is locally of finite type and geometrically integral, an invertible module $\mathcal{M}$ on $P \times_{\operatorname{Spec} k} T'$, and two sections $t_0, t_1$ of $h$ over $\operatorname{Spec} k$, such that the pullback of $\mathcal{M}$ along the base change of $t_0$ is isomorphic to the unit module, while its pullback along the base change of $t_1$ is isomorphic to the pullback of $\mathcal{L}$ along the first projection — then any non-zero morphism $s$ from the monoidal unit of the modules on $P$ to $\mathcal{L}$ forces $\mathcal{L}$ to be isomorphic to that unit.
--
--   This is the fibrewise triviality statement for line bundles algebraically equivalent to zero and possessing a non-zero global section, on the geometric fibres of the regular two-chart model of $X_1(Mp)$ over the valuation ring $A$; the fibre at the residue characteristic $p$ is the degeneration consisting of two smooth curves meeting transversally. It supplies the fibrewise hypothesis of the representability result for the algebraic-equivalence-zero cut of the relative Picard functor, and is cited by [`ModularCurve.XOneP.exists_representsRelSubPic_algEquivZeroCut_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_representsRelSubPic_algEquivZeroCut_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_nonempty_iso_unit_fibre_of_isAlgEquivZero_of_ne_zero_twoChartModel_x1_mul.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard

theorem ModularCurve.XOneP.nonempty_iso_unit_fibre_of_isAlgEquivZero_of_ne_zero_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    :
    ∀ (k : Type) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A))
      (L : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) x).Modules), Scheme.Modules.IsInvertible L →
      IsAlgEquivZero (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) x) L →
      ∀ s : 𝟙_ (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) x).Modules ⟶ L, s ≠ 0 → Nonempty (L ≅ 𝟙_ (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) x).Modules) := by sorry
