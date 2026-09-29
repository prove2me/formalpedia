-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_twoSidedPool_smoothLocus_closedPrime_two
-- name    : ModularCurve.DRModelPackageLevel.exists_twoSidedPool_smoothLocus_closedPrime_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/153a9030-d18c-59d1-af9e-74628c1974c3
-- title:
--   Two-sided étale pools in the smooth locus at q=2
-- statement:
--   Fix $N_0\ge 1$ and a prime $q$ with $q\nmid N_0$, a Deligne–Rapoport package $\mathfrak P$ of level data for the structure morphism `toBase N₀ q` $:$ `X N₀ q` $\to\operatorname{Spec}(R\,q)$, a prime $\mathfrak p$ of $R\,q$ with $\mathfrak p\neq(0)$, the assumption $q=2$, and natural numbers $A_0,B_0,n_0$. Then there exist $f\in R\,q$ with $f\notin\mathfrak p$, natural numbers $b,M,M'$ with $A_0b^{n_0}+B_0<M$ and $A_0b^{n_0}+B_0<M'$, a commutative ring $R'$ which is an $R\,q$-algebra and an algebra over $S:=$ `Localization.Away f` compatibly (scalar tower), module-finite, étale and faithfully flat over $S$, and two families of commutative rings $B_i$ ($i<M$) and $B'_i$ ($i<M'$), each module-finite and étale over $S$, with degrees $\deg i,\deg' i$ satisfying $1\le\deg\le b$, together with $R'$-algebra isomorphisms $R'\otimes_S B_i\simeq R'^{\deg i}$ and $R'\otimes_S B'_i\simeq R'^{\deg' i}$, and closed immersions $z_i:\operatorname{Spec}B_i\to \mathfrak X_S$, $z'_i:\operatorname{Spec}B'_i\to\mathfrak X_S$, where $\mathfrak X_S$ is the pullback of `toBase N₀ q` along $\operatorname{Spec}S\to\operatorname{Spec}(R\,q)$, such that: each $z_i$ (resp. $z'_i$) followed by the base-change projection $\mathfrak X_S\to\operatorname{Spec}S$ is the canonical map $\operatorname{Spec}B_i\to\operatorname{Spec}S$; the topological ranges of all $z_i$ and $z'_i$ lie in the preimage of the open set $\mathfrak P$`.smoothLocus` under the first projection; the ranges are pairwise disjoint within each family and mutually disjoint across the two families; $\deg' j\le 1$ for some $j$; for every algebraically closed field $k$, every $s:\operatorname{Spec}k\to\operatorname{Spec}S$ and every $i<M$, the preimage in the fibre $\mathfrak X_S\times_S k$ of the range of $z_i$ lies in the connected component, inside the trace of $\mathfrak P$`.smoothLocus` on that fibre, of the $k$-point obtained from the package's section $\varepsilon_\infty$ by base change to $S$ and passage to the fibre over $s$; and, for every such $k$, $s$ and every $i<M'$, provided the fibre over $s$ is not smooth, the preimage of the range of $z'_i$ lies in that trace minus the said connected component.
--
--   This is the $q=2$ case of the construction of "two-sided pools" of disjoint finite étale, locally split multisections in the smooth locus of the Deligne–Rapoport model of $X_0(N_0q)$ over $R\,q$, one family concentrated on the component of the cusp $\infty$ in each geometric fibre and one family avoiding it on the non-smooth fibres. The pools serve as input for the Zariski-local charts of the relative Picard functor, and the statement is used by [`ModularCurve.DRModelPackageLevel.exists_representsRelSubPic`](thm.html#ModularCurve.DRModelPackageLevel.exists_representsRelSubPic) and by the corresponding statement at the generic prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_twoSidedPool_smoothLocus_closedPrime_two.lean

import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve TensorProduct
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel

namespace ModularCurve.DRModelPackageLevel

theorem exists_twoSidedPool_smoothLocus_closedPrime_two (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (𝔭 : PrimeSpectrum (R q)) (h𝔭 : 𝔭.asIdeal ≠ ⊥) (hq : q = 2) (A₀ B₀ n₀ : ℕ) :
    ∃ (f : R q) (_ : f ∉ 𝔭.asIdeal) (b M M' : ℕ)
      (_ : A₀ * b ^ n₀ + B₀ < M) (_ : A₀ * b ^ n₀ + B₀ < M')
      (R' : Type) (_ : CommRing R') (_ : Algebra (R q) R')
      (_ : Algebra (Localization.Away f) R') (_ : IsScalarTower (R q) (Localization.Away f) R')
      (_ : Module.Finite (Localization.Away f) R') (_ : Algebra.Etale (Localization.Away f) R')
      (_ : Module.FaithfullyFlat (Localization.Away f) R')
      (B : Fin M → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra (Localization.Away f) (B i))
      (_ : ∀ i, Module.Finite (Localization.Away f) (B i)) (_ : ∀ i, Algebra.Etale (Localization.Away f) (B i))
      (deg : Fin M → ℕ) (_ : ∀ i, 1 ≤ deg i) (_ : ∀ i, deg i ≤ b)
      (φ : ∀ i, TensorProduct (Localization.Away f) R' (B i) ≃ₐ[R'] (Fin (deg i) → R'))
      (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback (toBase N₀ q) (specMap (R q) (Localization.Away f)))
      (_ : ∀ i, IsClosedImmersion (z i))
      (B' : Fin M' → Type) (_ : ∀ i, CommRing (B' i)) (_ : ∀ i, Algebra (Localization.Away f) (B' i))
      (_ : ∀ i, Module.Finite (Localization.Away f) (B' i)) (_ : ∀ i, Algebra.Etale (Localization.Away f) (B' i))
      (deg' : Fin M' → ℕ) (_ : ∀ i, 1 ≤ deg' i) (_ : ∀ i, deg' i ≤ b)
      (φ' : ∀ i, TensorProduct (Localization.Away f) R' (B' i) ≃ₐ[R'] (Fin (deg' i) → R'))
      (z' : ∀ i, Spec (CommRingCat.of (B' i)) ⟶ pullback (toBase N₀ q) (specMap (R q) (Localization.Away f)))
      (_ : ∀ i, IsClosedImmersion (z' i)),

      (∀ i, z i ≫ baseChange (R q) (toBase N₀ q) (Localization.Away f) = specMap (Localization.Away f) (B i)) ∧
      (∀ i, Set.range (z i).base ⊆
        ((pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f)) ⁻¹ᵁ 𝔓.smoothLocus : (pullback (toBase N₀ q) (specMap (R q) (Localization.Away f))).Opens) :
          Set ↥(pullback (toBase N₀ q) (specMap (R q) (Localization.Away f))))) ∧
      (Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base)) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
        (i : Fin M),
        (pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).base ⁻¹' Set.range (z i).base ⊆
          connectedComponentIn
            (((pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s ≫ pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))) ⁻¹ᵁ 𝔓.smoothLocus :
                (pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔓.εinf) s).1).base (IsLocalRing.closedPoint k))) ∧

      (∃ j, deg' j ≤ 1) ∧
      (∀ i, z' i ≫ baseChange (R q) (toBase N₀ q) (Localization.Away f) = specMap (Localization.Away f) (B' i)) ∧
      (∀ i, Set.range (z' i).base ⊆
        ((pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f)) ⁻¹ᵁ 𝔓.smoothLocus : (pullback (toBase N₀ q) (specMap (R q) (Localization.Away f))).Opens) :
          Set ↥(pullback (toBase N₀ q) (specMap (R q) (Localization.Away f))))) ∧
      (Pairwise fun i j => Disjoint (Set.range (z' i).base) (Set.range (z' j).base)) ∧
      (∀ i j, Disjoint (Set.range (z i).base) (Set.range (z' j).base)) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
        (i : Fin M'), ¬ Smooth (pullback.snd (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s) →
        (pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).base ⁻¹' Set.range (z' i).base ⊆
          (((pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s ≫ pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))) ⁻¹ᵁ 𝔓.smoothLocus :
                (pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s)) \
          connectedComponentIn
            (((pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s ≫ pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))) ⁻¹ᵁ 𝔓.smoothLocus :
                (pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔓.εinf) s).1).base (IsLocalRing.closedPoint k))) := by sorry
