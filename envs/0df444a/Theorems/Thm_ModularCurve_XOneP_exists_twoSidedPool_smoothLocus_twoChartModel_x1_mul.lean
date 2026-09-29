-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_twoSidedPool_smoothLocus_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_twoSidedPool_smoothLocus_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/ba6ebc73-2507-58f5-846b-07bbbeb2a7ea
-- title:
--   Two-sided pools of étale multisections on the X₁(Mp) two-chart model
-- statement:
--   Fix a prime $p$, an integer $M\ge 5$ with $p\nmid M$, a field $L$ of characteristic zero which is a $\{p\}$-cyclotomic extension of $\mathbb{Q}$, and a primitive $p$-th root of unity $\zeta\in L$. Let $K$ be the intermediate field of $L((q))$ obtained by adjoining to $L$ the coefficientwise image of the function field `x1FunctionField (M * p)` of $X_1(Mp)$ over $\mathbb{Q}$, and let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ and $\zeta$ is in the image of $A$, with $K$ an $A$-algebra compatibly with $L$. Let $j\in K$ be the element whose Laurent expansion is the image of the $q$-expansion `jq` of the $j$-invariant, assumed nonzero, and write $\pi\colon X=$ `TwoChartModel A K j` $\to\operatorname{Spec}A$ for the structure map `TwoChart.modelTo`, i.e. the map out of the pushout of the two charts. Let $U\subseteq X$ be an open subscheme such that the composite of its inclusion with $\pi$ is smooth of relative dimension $1$ and which contains every such open, and let $\varepsilon$ be a section of $\pi$ (a morphism $\operatorname{Spec}A\to X$ over the identity) whose image lies in $U$. The conclusion asserts: for every prime $\mathfrak{p}$ of $A$ and all naturals $A_0,B_0,n_0$ there exist $f\in A\setminus\mathfrak{p}$, a degree bound $b$, and sizes $M,M'$ with $A_0b^{n_0}+B_0<M$ and $A_0b^{n_0}+B_0<M'$, together with a finite étale faithfully flat $A_f$-algebra $R'$ (where $A_f=$ `Localization.Away f`), two families of finite étale $A_f$-algebras $B_i$ ($i<M$) and $B'_i$ ($i<M'$) with degrees $\deg i,\deg' i$ between $1$ and $b$, $R'$-algebra isomorphisms $R'\otimes_{A_f}B_i\cong R'^{\deg i}$ and $R'\otimes_{A_f}B'_i\cong R'^{\deg' i}$, and closed immersions $z_i\colon\operatorname{Spec}B_i\to X_{A_f}$, $z'_i\colon\operatorname{Spec}B'_i\to X_{A_f}$ into the pullback of $\pi$ along $\operatorname{Spec}A_f\to\operatorname{Spec}A$, such that: each $z_i$ and each $z'_i$ is a section of $X_{A_f}\to\operatorname{Spec}A_f$ over the structure map of $B_i$ resp. $B'_i$; the images of all $z_i$ and $z'_i$ lie in the preimage of $U$; the $z_i$ have pairwise disjoint images, the $z'_i$ have pairwise disjoint images, and each $z_i$-image is disjoint from each $z'_j$-image; at least one $\deg' j$ is $\le 1$; for every algebraically closed field $k$ and every $k$-point $s$ of $\operatorname{Spec}A_f$, the preimage in the geometric fibre of each $\operatorname{range}(z_i)$ lies in the connected component, inside the preimage of $U$, of the point cut out by the base change of $\varepsilon$ via `sectionFibrePoint`; and, whenever that geometric fibre is not smooth, the preimage of each $\operatorname{range}(z'_i)$ lies in the preimage of $U$ minus that component.
--
--   This supplies, for the regular two-chart model of $X_1(Mp)$ over a discrete valuation ring containing $\zeta_p$, the "two-sided pool" datum of arbitrarily many disjoint finite étale multisections of bounded degree, split by a common étale cover, half of them on the identity component of each geometric fibre and half off it on the non-smooth fibres. It is used by [`ModularCurve.XOneP.exists_representsRelSubPic_algEquivZeroCut_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_representsRelSubPic_algEquivZeroCut_twoChartModel_x1_mul) in the analysis of the relative Picard functor and the component group of the special fibre, and is obtained from the one-sided pool statement together with the automorphism of the model that exchanges the two components of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_twoSidedPool_smoothLocus_twoChartModel_x1_mul.lean

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

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian

theorem ModularCurve.XOneP.exists_twoSidedPool_smoothLocus_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (U : (ModularCurve.TwoChartModel A (↥K) j).Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j))]
    (hUmax : ∀ W : (ModularCurve.TwoChartModel A (↥K) j).Opens, SmoothOfRelativeDimension 1 (W.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j)) → W ≤ U)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j)) (hε : Set.range ε.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j)))
    :
    ∀ (𝔭 : PrimeSpectrum A) (A₀ B₀ n₀ : ℕ), ∃ (f : A) (_ : f ∉ 𝔭.asIdeal) (b M M' : ℕ)
      (_ : A₀ * b ^ n₀ + B₀ < M) (_ : A₀ * b ^ n₀ + B₀ < M')
      (R' : Type) (_ : CommRing R') (_ : Algebra A R')
      (_ : Algebra (Localization.Away f) R') (_ : IsScalarTower A (Localization.Away f) R')
      (_ : Module.Finite (Localization.Away f) R') (_ : Algebra.Etale (Localization.Away f) R')
      (_ : Module.FaithfullyFlat (Localization.Away f) R')
      (B : Fin M → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra (Localization.Away f) (B i))
      (_ : ∀ i, Module.Finite (Localization.Away f) (B i)) (_ : ∀ i, Algebra.Etale (Localization.Away f) (B i))
      (deg : Fin M → ℕ) (_ : ∀ i, 1 ≤ deg i) (_ : ∀ i, deg i ≤ b)
      (φ : ∀ i, TensorProduct (Localization.Away f) R' (B i) ≃ₐ[R'] (Fin (deg i) → R'))
      (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (Localization.Away f)))
      (_ : ∀ i, IsClosedImmersion (z i))
      (B' : Fin M' → Type) (_ : ∀ i, CommRing (B' i)) (_ : ∀ i, Algebra (Localization.Away f) (B' i))
      (_ : ∀ i, Module.Finite (Localization.Away f) (B' i)) (_ : ∀ i, Algebra.Etale (Localization.Away f) (B' i))
      (deg' : Fin M' → ℕ) (_ : ∀ i, 1 ≤ deg' i) (_ : ∀ i, deg' i ≤ b)
      (φ' : ∀ i, TensorProduct (Localization.Away f) R' (B' i) ≃ₐ[R'] (Fin (deg' i) → R'))
      (z' : ∀ i, Spec (CommRingCat.of (B' i)) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (Localization.Away f)))
      (_ : ∀ i, IsClosedImmersion (z' i)),

      (∀ i, z i ≫ baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f) = specMap (Localization.Away f) (B i)) ∧
      (∀ i, Set.range (z i).base ⊆
        ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (Localization.Away f)) ⁻¹ᵁ U : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (Localization.Away f))).Opens) :
          Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (Localization.Away f))))) ∧
      (Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base)) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
        (i : Fin M),
        (pullback.fst (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s).base ⁻¹' Set.range (z i).base ⊆
          connectedComponentIn
            (((pullback.fst (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (Localization.Away f))) ⁻¹ᵁ U :
                (pullback (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) ε) s).1).base (IsLocalRing.closedPoint k))) ∧

      (∃ j, deg' j ≤ 1) ∧
      (∀ i, z' i ≫ baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f) = specMap (Localization.Away f) (B' i)) ∧
      (∀ i, Set.range (z' i).base ⊆
        ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (Localization.Away f)) ⁻¹ᵁ U : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (Localization.Away f))).Opens) :
          Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (Localization.Away f))))) ∧
      (Pairwise fun i j => Disjoint (Set.range (z' i).base) (Set.range (z' j).base)) ∧
      (∀ i j, Disjoint (Set.range (z i).base) (Set.range (z' j).base)) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
        (i : Fin M'), ¬ Smooth (pullback.snd (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s) →
        (pullback.fst (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s).base ⁻¹' Set.range (z' i).base ⊆
          (((pullback.fst (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (Localization.Away f))) ⁻¹ᵁ U :
                (pullback (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s)) \
          connectedComponentIn
            (((pullback.fst (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (Localization.Away f))) ⁻¹ᵁ U :
                (pullback (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) ε) s).1).base (IsLocalRing.closedPoint k))) := by sorry
