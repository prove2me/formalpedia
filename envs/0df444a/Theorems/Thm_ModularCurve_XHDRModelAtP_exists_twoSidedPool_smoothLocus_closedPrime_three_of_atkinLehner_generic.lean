-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_twoSidedPool_smoothLocus_closedPrime_three_of_atkinLehner_generic
-- name    : ModularCurve.XHDRModelAtP.exists_twoSidedPool_smoothLocus_closedPrime_three_of_atkinLehner_generic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/4b454b67-3d07-5921-b2c2-924b5268f49b
-- title:
--   Two-sided pools of étale blocks at the closed prime, p=3
-- statement:
--   Fix natural numbers $p$, $M$ with $p$ prime and $M \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, hypotheses $p \mid M$ and $p^{2} \nmid M$, and the hypothesis `hHp` that every unit of $\mathbb{Z}/M$ mapping to $1$ under the reduction $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/(M/p))^{\times}$ lies in $H$; let `hj` assert that the $q$-series `jqModC ℚ` of $j$ lies in the field `qExpFunctionFieldC ℚ ⊤` of $q$-expansions of ratios of integral modular forms, and let $\mathfrak{X}$ be a Deligne–Rapoport model bundle `XHDRModelAtP p M H hpM hj` for $X_H(M)$ over $R_p$, with its Atkin–Lehner isomorphism $\mathfrak{X}.w$, cusp section $\mathfrak{X}.\varepsilon_{\infty}$, open smooth locus $\mathfrak{X}.\mathrm{smoothLocus}$ and geometric curve model $\mathfrak{X}.\mathrm{Meta}$ over $\overline{\mathbb{Q}}$ with function field `xHFunctionFieldBar M H`. Further data: a $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of that function field satisfying `hθ`, namely that whenever $f$ has the same Laurent series as an element $u$ of `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` (the level-$M/p$ field for the image of $H$), the series of $\theta f$ is `qExpand` of that of $u$, i.e. $q \mapsto q^{p}$; and `hwgen`, asserting that for any two $\overline{\mathbb{Q}}$-points $y$, $y'$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base, if $y'$ followed by $\mathfrak{X}.\mathrm{eeta}$, the first projection and $\mathfrak{X}.w$ agrees with $y$ followed by $\mathfrak{X}.\mathrm{eeta}$ and the first projection, then the place attached to $y'$ is the translate of the place attached to $y$ by the semilinear automorphism `SemilinearAut.ofAlgAut θ`. Finally let $\mathfrak{p}$ be a prime of $R_p$ with non-zero prime ideal, assume $p = 3$, and let $A_0$, $B_0$, $n_0$ be natural numbers. The conclusion asserts the existence of $f \in R_p \setminus \mathfrak{p}$ and natural numbers $b$, $N_1$, $N_2$ with $A_0 b^{n_0} + B_0 < N_1$ and $A_0 b^{n_0} + B_0 < N_2$; a commutative ring $R'$ which is an $R_p$-algebra and a $\mathrm{Localization.Away}\ f$-algebra compatibly, module-finite, étale and faithfully flat over $\mathrm{Localization.Away}\ f$; families of rings $B_i$ ($i \in \mathrm{Fin}\ N_1$) and $B'_i$ ($i \in \mathrm{Fin}\ N_2$), each finite étale over $\mathrm{Localization.Away}\ f$, with degrees $\deg i$, $\deg' i$ in $[1, b]$ and $R'$-algebra isomorphisms $R' \otimes B_i \cong R'^{\deg i}$, $R' \otimes B'_i \cong R'^{\deg' i}$; and closed immersions $z_i : \operatorname{Spec} B_i \to \mathfrak{X}_{f}$, $z'_i : \operatorname{Spec} B'_i \to \mathfrak{X}_{f}$ into the base change of `toBase p (ΓM M H) hj` along $\operatorname{Spec} \mathrm{Localization.Away}\ f \to \operatorname{Spec} R_p$, such that: each $z_i$ and each $z'_i$ is a morphism over $\mathrm{Localization.Away}\ f$; all their images lie in the preimage of $\mathfrak{X}.\mathrm{smoothLocus}$ under the first projection; the images of the $z_i$ are pairwise disjoint, likewise those of the $z'_i$, and every $z_i$-image is disjoint from every $z'_j$-image; some $\deg' j \le 1$; for every algebraically closed field $k$, every $k$-point $s$ of $\operatorname{Spec} \mathrm{Localization.Away}\ f$ and every $i \in \mathrm{Fin}\ N_1$, the preimage in the fibre over $s$ of the image of $z_i$ lies in the connected component, inside the preimage of $\mathfrak{X}.\mathrm{smoothLocus}$, of the point cut out by the base-changed cusp section $\mathfrak{X}.\varepsilon_{\infty}$ at the closed point of $k$; and, for every such $k$ and $s$ for which the fibre morphism is not smooth and every $i \in \mathrm{Fin}\ N_2$, the preimage in that fibre of the image of $z'_i$ lies in the preimage of $\mathfrak{X}.\mathrm{smoothLocus}$ with that cusp component removed.
--
--   This is the $p = 3$, closed-prime case of the production of "two-sided pools": two large families of rational finite étale blocks of bounded degree in the smooth locus of the Deligne–Rapoport model of $X_H(M)$ over $\mathbb{Z}_{(p)}[1/f]$, one family concentrated on the component of the cusp $\infty$ in every degenerate geometric fibre and the other avoiding it, with the number of blocks exceeding the prescribed bound $A_0 b^{n_0} + B_0$. It feeds the corresponding statement at a generic prime of $R_p$ and the combined pool statement used in the relative Picard and Néron model analysis of the $\Gamma_H$-model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_twoSidedPool_smoothLocus_closedPrime_three_of_atkinLehner_generic.lean

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

theorem ModularCurve.XHDRModelAtP.exists_twoSidedPool_smoothLocus_closedPrime_three_of_atkinLehner_generic
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
    (𝔭 : PrimeSpectrum (R p)) (h𝔭 : 𝔭.asIdeal ≠ ⊥) (hp3 : p = 3) (A₀ B₀ n₀ : ℕ) :
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
