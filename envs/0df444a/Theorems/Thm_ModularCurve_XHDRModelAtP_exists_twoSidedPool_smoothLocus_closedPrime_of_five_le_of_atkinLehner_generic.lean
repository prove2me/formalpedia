-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_twoSidedPool_smoothLocus_closedPrime_of_five_le_of_atkinLehner_generic
-- name    : ModularCurve.XHDRModelAtP.exists_twoSidedPool_smoothLocus_closedPrime_of_five_le_of_atkinLehner_generic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/1439ee87-8d2c-51cf-9e70-a45a3b4a8935
-- title:
--   Two-sided pools of étale blocks at the closed prime
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ and $p^2 \nmid M$, and let $H \le (\mathbb{Z}/M)^\times$ contain the whole kernel of the reduction map `ZMod.unitsMap` from $(\mathbb{Z}/M)^\times$ to $(\mathbb{Z}/(M/p))^\times$; assume the $q$-series $j$ lies in the level-one $q$-expansion field `qExpFunctionFieldC ℚ ⊤`, and let $\mathfrak{X}$ be an `XHDRModelAtP p M H hpM hj`, i.e. a package carrying the proper, flat, integral, normal model `X p (ΓM M H) hj` over $R_p$, its open smooth locus `𝔛.smoothLocus`, a self-isomorphism `𝔛.w`, a section `𝔛.εinf`, and an identification `𝔛.Meta` of its geometric generic fibre with a curve model of $\overline{F}_H(M)$ = `xHFunctionFieldBar M H`. Let $\theta$ be an $\overline{\mathbb{Q}}$-algebra automorphism of $\overline{F}_H(M)$ which, on any element whose Laurent series comes from level $M/p$ with character group `infSubgroup p M H hpM`, acts by the substitution $q \mapsto q^p$ (`qExpand`), and assume `hwgen`: whenever two $\overline{\mathbb{Q}}$-points of `𝔛.Meta.C` over the base are related by $\mathfrak{X}.w$ after transport along `𝔛.eeta` and the first projection, their associated places are related by the semilinear automorphism `SemilinearAut.ofAlgAut θ`. Let $\mathfrak{p}$ be a prime of $R_p$ with nonzero ideal, suppose $5 \le p$, and fix naturals $A_0, B_0, n_0$. Then there exist $f \in R_p \setminus \mathfrak{p}$, naturals $b$, $N_1$, $N_2$ with $A_0 b^{n_0} + B_0 < N_1, N_2$, a ring $R'$ that is a finite étale faithfully flat algebra over $R_p[1/f] =$ `Localization.Away f` (compatibly with $R_p$), and two families of finite étale $R_p[1/f]$-algebras $B_i$ ($i \in \mathrm{Fin}\,N_1$) and $B'_i$ ($i \in \mathrm{Fin}\,N_2$) with degrees $\deg i, \deg' i \in [1,b]$, together with $R'$-algebra isomorphisms $R' \otimes B_i \cong R'^{\deg i}$ and $R' \otimes B'_i \cong R'^{\deg' i}$, and closed immersions $z_i : \operatorname{Spec} B_i \to \mathfrak{X}[1/f]$, $z'_i : \operatorname{Spec} B'_i \to \mathfrak{X}[1/f]$ into the base change of `toBase p (ΓM M H) hj` along $\operatorname{Spec} R_p[1/f] \to \operatorname{Spec} R_p$, such that: all $z_i$ and $z'_i$ are morphisms over $\operatorname{Spec} R_p[1/f]$; their images lie in the preimage of `𝔛.smoothLocus`; the images of the $z_i$ are pairwise disjoint, those of the $z'_i$ are pairwise disjoint, and every $z_i$-image is disjoint from every $z'_j$-image; for every algebraically closed field $k$ and every point $s : \operatorname{Spec} k \to \operatorname{Spec} R_p[1/f]$ and every $i$, the part of the fibre over $s$ lying above the image of $z_i$ is contained in the connected component, inside the smooth locus of that fibre, of the point cut out by the base change of the section `𝔛.εinf`; some $\deg' j \le 1$; and for every such $k$, $s$ with non-smooth fibre and every $i$, the part of the fibre above the image of $z'_i$ lies in the smooth locus of the fibre with that connected component of the `𝔛.εinf`-point removed.
--
--   This is the production of "two-sided pools" of $R_p[1/f]$-rational finite étale blocks of bounded degree in the smooth locus of the Deligne–Rapoport model of $X_H(M)$ at the closed prime of $R_p$, one family concentrated on the component of the cusp section $\varepsilon_\infty$ and one family avoiding it on non-smooth fibres, with degrees split by a single finite étale cover $R'$ and cardinalities exceeding a prescribed polynomial bound $A_0 b^{n_0} + B_0$. It is the closed-prime case feeding [`ModularCurve.XHDRModelAtP.exists_twoSidedPool_smoothLocus_genericPrime_of_atkinLehner_generic`](thm.html#ModularCurve.XHDRModelAtP.exists_twoSidedPool_smoothLocus_genericPrime_of_atkinLehner_generic) and [`ModularCurve.XHDRModelAtP.exists_twoSided_pools_smoothLocus_of_atkinLehner_generic_of_ker_le`](thm.html#ModularCurve.XHDRModelAtP.exists_twoSided_pools_smoothLocus_of_atkinLehner_generic_of_ker_le), where such pools drive the relative Picard and component-group bookkeeping at the Atkin–Lehner involution.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_twoSidedPool_smoothLocus_closedPrime_of_five_le_of_atkinLehner_generic.lean

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

theorem ModularCurve.XHDRModelAtP.exists_twoSidedPool_smoothLocus_closedPrime_of_five_le_of_atkinLehner_generic
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
        𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (𝔭 : PrimeSpectrum (R p)) (h𝔭 : 𝔭.asIdeal ≠ ⊥) (hp5 : 5 ≤ p) (A₀ B₀ n₀ : ℕ) :
    ∃ (f : R p) (_ : f ∉ 𝔭.asIdeal) (b N₁ N₂ : ℕ)
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

      (∃ j, deg' j ≤ 1) ∧
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
