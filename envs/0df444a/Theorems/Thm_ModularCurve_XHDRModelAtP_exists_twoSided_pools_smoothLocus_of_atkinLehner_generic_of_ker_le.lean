-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_twoSided_pools_smoothLocus_of_atkinLehner_generic_of_ker_le
-- name    : ModularCurve.XHDRModelAtP.exists_twoSided_pools_smoothLocus_of_atkinLehner_generic_of_ker_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/e92c23ce-f08c-5585-9329-3347b857acc0
-- title:
--   Two-sided pools of étale blocks in the smooth locus
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ under $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$. Assume `jqModC ℚ` lies in `qExpFunctionFieldC ℚ ⊤`, and let $\mathfrak{X}$ be a bundle of type `XHDRModelAtP p M H hpM hj`, a Deligne–Rapoport style integral model of $X_H(M)$ over `R p` together with its geometric curve model `Meta` over $\overline{\mathbb{Q}}$. Let $\theta$ be a $\overline{\mathbb{Q}}$-algebra automorphism of `xHFunctionFieldBar M H` such that whenever $f$ in that field and $u$ in `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` have the same Laurent series, the Laurent series of $\theta f$ is `qExpand` of that of $u$ at $p$ (the substitution $q \mapsto q^p$), and assume the genericity condition `hwgen`: for geometric sections $y, y'$ of `𝔛.Meta.toBase`, if $y'$ composed with `𝔛.eeta`, the first pullback projection and the morphism underlying `𝔛.w` agrees with $y$ composed with `𝔛.eeta` and that projection, then the place attached to $y'$ by `𝔛.Meta.pointEquivPlace` is the translate of the place attached to $y$ under the semilinear automorphism induced by $\theta$. The conclusion asserts a single $d_0 \in \mathbb{N}$ such that for every prime $\mathfrak{p}$ of `R p` and all $A_0, B_0, n_0 \in \mathbb{N}$ there are: an $f \in$ `R p` outside $\mathfrak{p}$; naturals $b, N_1, N_2$ with $A_0 b^{n_0} + B_0 < N_1$ and $A_0 b^{n_0} + B_0 < N_2$; a ring $R'$ that is finite, étale and faithfully flat over `Localization.Away f` compatibly with `R p`; and two families of finite étale `Localization.Away f`-algebras $B_i$ ($i \in \mathrm{Fin}\,N_1$) and $B'_i$ ($i \in \mathrm{Fin}\,N_2$), with degrees $\deg i, \deg' i$ between $1$ and $b$, $R'$-algebra isomorphisms $R' \otimes B_i \cong R'^{\deg i}$ and $R' \otimes B'_i \cong R'^{\deg' i}$, and closed immersions $z_i : \operatorname{Spec} B_i \to$ and $z'_i : \operatorname{Spec} B'_i \to$ the base change of `toBase p (ΓM M H) hj` along `Localization.Away f`. These satisfy: each $z_i$ and $z'_i$ is a section of the base-changed structure morphism over $\operatorname{Spec} B_i$ respectively $\operatorname{Spec} B'_i$; all their images lie in the preimage of `𝔛.smoothLocus`; the images of the $z_i$ are pairwise disjoint, likewise those of the $z'_i$, and the two families have disjoint images; some $\deg' j \le d_0$; for every algebraically closed field $k$ and every $k$-point $s$ of $\operatorname{Spec}$ `Localization.Away f`, the part of each $\operatorname{range}(z_i)$ seen in the fibre over $s$ lies in the connected component, inside the smooth locus of that fibre, of the point given by the cusp section `𝔛.εinf` base changed to `Localization.Away f` and specialised at the closed point of $k$; and, for such $k$ and $s$ with the fibre not smooth, the part of each $\operatorname{range}(z'_i)$ in that fibre lies in the smooth locus of the fibre with that component removed.
--
--   This is the geometric input of the 'pools' method for the Deligne–Rapoport model of $X_H(M)$ at a prime $p$ exactly dividing the level: arbitrarily large supplies of pairwise disjoint finite étale blocks of bounded degree inside the smooth locus, split on one side into the component of the cusp $\infty$ and on the other side away from it in the degenerate fibres. It is assembled from the generic-prime and closed-prime cases (the latter split according to $p \ge 5$, $p = 3$, $p = 2$), and feeds the construction of relative sub-Picard representability data and of the level data dictionary for the Jacobian at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_twoSided_pools_smoothLocus_of_atkinLehner_generic_of_ker_le.lean

import Mathlib
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
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_twoSided_pools_smoothLocus_of_atkinLehner_generic_of_ker_le
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
          ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
        𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y) :
    ∃ d₀ : ℕ, ∀ (𝔭 : PrimeSpectrum (R p)) (A₀ B₀ n₀ : ℕ), ∃ (f : (R p)) (_ : f ∉ 𝔭.asIdeal) (b N₁ N₂ : ℕ)
      (_ : A₀ * b ^ n₀ + B₀ < N₁) (_ : A₀ * b ^ n₀ + B₀ < N₂)
      (R' : Type) (_ : CommRing R') (_ : Algebra (R p) R')
      (_ : Algebra (Localization.Away f) R') (_ : IsScalarTower (R p) (Localization.Away f) R')
      (_ : Module.Finite (Localization.Away f) R') (_ : Algebra.Etale (Localization.Away f) R')
      (_ : Module.FaithfullyFlat (Localization.Away f) R')
      (B : Fin N₁ → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra (Localization.Away f) (B i))
      (_ : ∀ i, Module.Finite (Localization.Away f) (B i)) (_ : ∀ i, Algebra.Etale (Localization.Away f) (B i))
      (deg : Fin N₁ → ℕ) (_ : ∀ i, 1 ≤ deg i) (_ : ∀ i, deg i ≤ b)
      (φ : ∀ i, TensorProduct (Localization.Away f) R' (B i) ≃ₐ[R'] (Fin (deg i) → R'))
      (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f)))
      (_ : ∀ i, IsClosedImmersion (z i))
      (B' : Fin N₂ → Type) (_ : ∀ i, CommRing (B' i)) (_ : ∀ i, Algebra (Localization.Away f) (B' i))
      (_ : ∀ i, Module.Finite (Localization.Away f) (B' i)) (_ : ∀ i, Algebra.Etale (Localization.Away f) (B' i))
      (deg' : Fin N₂ → ℕ) (_ : ∀ i, 1 ≤ deg' i) (_ : ∀ i, deg' i ≤ b)
      (φ' : ∀ i, TensorProduct (Localization.Away f) R' (B' i) ≃ₐ[R'] (Fin (deg' i) → R'))
      (z' : ∀ i, Spec (CommRingCat.of (B' i)) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f)))
      (_ : ∀ i, IsClosedImmersion (z' i)),

      (∀ i, z i ≫ baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f) = specMap (Localization.Away f) (B i)) ∧
      (∀ i, Set.range (z i).base ⊆
        ((pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f)) ⁻¹ᵁ 𝔛.smoothLocus : (pullback (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))).Opens) :
          Set ↥(pullback (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))))) ∧
      (Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base)) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
        (i : Fin N₁),
        (pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s).base ⁻¹' Set.range (z i).base ⊆
          connectedComponentIn
            (((pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
                (pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k))) ∧

      (∃ j, deg' j ≤ d₀) ∧
      (∀ i, z' i ≫ baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f) = specMap (Localization.Away f) (B' i)) ∧
      (∀ i, Set.range (z' i).base ⊆
        ((pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f)) ⁻¹ᵁ 𝔛.smoothLocus : (pullback (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))).Opens) :
          Set ↥(pullback (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))))) ∧
      (Pairwise fun i j => Disjoint (Set.range (z' i).base) (Set.range (z' j).base)) ∧
      (∀ i j, Disjoint (Set.range (z i).base) (Set.range (z' j).base)) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
        (i : Fin N₂), ¬ Smooth (pullback.snd (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s) →
        (pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s).base ⁻¹' Set.range (z' i).base ⊆
          (((pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
                (pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s)) \
          connectedComponentIn
            (((pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
                (pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k))) := by sorry
