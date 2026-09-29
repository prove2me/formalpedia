-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_twoSidedPool_smoothLocus_closedPrime_of_five_le
-- name    : ModularCurve.DRModelPackageLevel.exists_twoSidedPool_smoothLocus_closedPrime_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/48462d8f-0257-5cb6-b4a2-34f63893ba9c
-- title:
--   Two-sided étale pools in the smooth locus for q≥ 5
-- statement:
--   Let $N_0\ge 1$ and let $q$ be a prime with $q\nmid N_0$, let $\mathfrak P$ be a `DRModelPackageLevel` datum for $N_0,q$ — a proper, flat, locally finitely presented structure morphism `toBase N₀ q` from the integral Igusa-type scheme $X(N_0,q)$ to $\operatorname{Spec}(R_q)$, with normality on affine opens, an identification of its base change to $\overline{\mathbf Q}$ with a curve model of the modular function field of level $N_0q$ together with Galois equivariance and chart pinning, smoothness of relative dimension $1$ and geometric integrality of the generic fibre, cusp sections `εinf`, `εzero`, and a distinguished open `smoothLocus` — let $\mathfrak p$ be a prime of $R_q$ with $\mathfrak p\neq(0)$, assume $5\le q$, and let $A_0,B_0,n_0$ be natural numbers. Then there exist $f\in R_q$ with $f\notin\mathfrak p$, natural numbers $b,M,M'$ with $A_0b^{n_0}+B_0<M$ and $A_0b^{n_0}+B_0<M'$, a commutative ring $R'$ that is an $R_q$-algebra and an algebra over $R_f:=$ `Localization.Away f` compatibly (scalar tower), module-finite, étale and faithfully flat over $R_f$, and two families of commutative rings $B_i$ ($i<M$) and $B'_i$ ($i<M'$), each module-finite and étale over $R_f$, with degrees $\deg i,\deg' i$ satisfying $1\le\deg i\le b$ and $1\le \deg' i\le b$, $R'$-algebra isomorphisms $R'\otimes_{R_f}B_i\cong (R')^{\deg i}$ and $R'\otimes_{R_f}B'_i\cong (R')^{\deg' i}$, and closed immersions $z_i:\operatorname{Spec}B_i\to \mathfrak X_f$, $z'_i:\operatorname{Spec}B'_i\to\mathfrak X_f$ into the base change $\mathfrak X_f=X(N_0,q)\times_{\operatorname{Spec}R_q}\operatorname{Spec}R_f$, such that: each $z_i$ and each $z'_i$ is a morphism over $\operatorname{Spec}R_f$ (composition with the projection `baseChange` equals the structure map of $B_i$, resp. $B'_i$); all their images lie in the preimage of `𝔓.smoothLocus` under the first projection; the images within each family are pairwise disjoint and images from the two families are disjoint; for every algebraically closed field $k$, every $s:\operatorname{Spec}k\to\operatorname{Spec}R_f$ and every $i<M$, the preimage of the image of $z_i$ in the fibre $\mathfrak X_f\times_{\operatorname{Spec}R_f}\operatorname{Spec}k$ is contained in the connected component, inside the trace of `𝔓.smoothLocus` on that fibre, of the point cut out by the base-changed cusp section `εinf` at the closed point of $\operatorname{Spec}k$; some $j$ has $\deg' j\le 1$; and for every such $k$ and $s$ for which the fibre is not smooth, and every $i<M'$, the preimage of the image of $z'_i$ lies in the trace of `𝔓.smoothLocus` with that connected component removed.
--
--   This supplies, at the closed prime of $R_q$ and under the assumption $q\ge 5$, the pool of pairwise disjoint finite étale multisections in the smooth locus of the Deligne–Rapoport model — arbitrarily many lying on the component of the cusp $\infty$ in each geometric fibre, and arbitrarily many, one of them of degree at most one, lying off that component on the non-smooth fibres — in general position as required for Zariski-local charts of the relative Picard functor. It is one of the case branches feeding [`ModularCurve.DRModelPackageLevel.exists_representsRelSubPic`](thm.html#ModularCurve.DRModelPackageLevel.exists_representsRelSubPic) and [`ModularCurve.DRModelPackageLevel.exists_twoSidedPool_smoothLocus_genericPrime`](thm.html#ModularCurve.DRModelPackageLevel.exists_twoSidedPool_smoothLocus_genericPrime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_twoSidedPool_smoothLocus_closedPrime_of_five_le.lean

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

theorem exists_twoSidedPool_smoothLocus_closedPrime_of_five_le (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (𝔭 : PrimeSpectrum (R q)) (h𝔭 : 𝔭.asIdeal ≠ ⊥) (hq : 5 ≤ q) (A₀ B₀ n₀ : ℕ) :
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
