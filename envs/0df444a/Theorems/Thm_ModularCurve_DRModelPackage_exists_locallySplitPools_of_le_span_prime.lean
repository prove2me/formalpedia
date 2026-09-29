-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_exists_locallySplitPools_of_le_span_prime
-- name    : ModularCurve.DRModelPackage.exists_locallySplitPools_of_le_span_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/563d422e-ecd9-50fb-a88d-684c30bef482
-- title:
--   Locally split pools at primes above p
-- statement:
--   Let $p$ be a prime with $5 \le p$, let $\mathfrak X$ be a `DRModelPackage p` — a package consisting of the two-chart integral model `DRModel p` of the full modular function field of level $p$ over $\mathbb Z$ together with properness, flatness, integrality and normality of `DRModel.toBase p`, identifications of its rational and geometric generic fibres with curve models, two sections $\varepsilon_\infty,\varepsilon_0$ of `DRModel.toBase p`, and a distinguished open `𝔛.smoothLocus` that is smooth of relative dimension $1$ over $\mathbb Z$ and contains every smooth open — let $\mathfrak p$ be a point of $\operatorname{Spec}\mathbb Z$ whose prime ideal is contained in $(p)$, and let $A_0,B_0,n_0$ be natural numbers. Then there exist $f \in \mathbb Z$ with $f \notin \mathfrak p$ and natural numbers $b, M$ with $A_0 b^{n_0} + B_0 < M$, a ring $R'$ that is an algebra over $\mathbb Z$ and over $\mathbb Z[1/f] =$ `Localization.Away f` compatibly, and which is finite, étale and faithfully flat over $\mathbb Z[1/f]$, together with rings $B_i$ for $i \in \mathrm{Fin}\,M$, each finite étale over $\mathbb Z[1/f]$, degrees $\deg i$ with $1 \le \deg i \le b$, $R'$-algebra isomorphisms $R' \otimes_{\mathbb Z[1/f]} B_i \cong R'^{\deg i}$, and closed immersions $z_i \colon \operatorname{Spec} B_i \to \mathfrak X_{\mathbb Z[1/f]} := \operatorname{Spec}\mathbb Z[1/f] \times_{\operatorname{Spec}\mathbb Z} \mathrm{DRModel}\,p$, such that: each $z_i$ followed by the projection to $\operatorname{Spec}\mathbb Z[1/f]$ is the structure morphism of $B_i$; the image of each $z_i$ on points lies in the preimage of `𝔛.smoothLocus` under the first projection; the images of the $z_i$ are pairwise disjoint; and for every algebraically closed field $k$, every $s \colon \operatorname{Spec} k \to \operatorname{Spec}\mathbb Z[1/f]$ and every $i$, the preimage in the fibre $\mathfrak X_{\mathbb Z[1/f]} \times_{\operatorname{Spec}\mathbb Z[1/f]} \operatorname{Spec} k$ of the image of $z_i$ is contained in the connected component, inside the preimage of `𝔛.smoothLocus` in that fibre, of the point obtained from the section $\varepsilon_\infty$ base-changed to $\mathbb Z[1/f]$ and restricted to the fibre over $s$, evaluated at the closed point of $\operatorname{Spec} k$.
--
--   This supplies, for the primes $\mathfrak p \subseteq (p)$ of $\mathbb Z$, the existence of arbitrarily large families of pairwise disjoint finite étale "pools" of bounded degree inside the smooth locus of the Deligne–Rapoport model, all lying geometrically in the connected component of the cusp $\infty$; the pools arise as level sets of Ogg's modular unit. It is the $p$-adic and generic input to [`ModularCurve.DRModelPackage.exists_locallySplitPools_of_five_le`](thm.html#ModularCurve.DRModelPackage.exists_locallySplitPools_of_five_le), which assembles the same conclusion at all primes of $\mathbb Z$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_exists_locallySplitPools_of_le_span_prime.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicCurve IsLocalRing

theorem ModularCurve.DRModelPackage.exists_locallySplitPools_of_le_span_prime
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p) (𝔭 : PrimeSpectrum ℤ) (A₀ B₀ n₀ : ℕ)
    (h𝔭p : 𝔭.asIdeal ≤ Ideal.span {(p : ℤ)}) :
    ∃ (f : ℤ) (_ : f ∉ 𝔭.asIdeal) (b M : ℕ) (_ : A₀ * b ^ n₀ + B₀ < M)
    (R' : Type) (_ : CommRing R') (aZ : Algebra ℤ R')
    (aL : Algebra (Localization.Away f) R')

    (_ : @IsScalarTower ℤ (Localization.Away f) R' OreLocalization.instSMulOfIsScalarTower aL.toSMul aZ.toSMul)
    (_ : Module.Finite (Localization.Away f) R') (_ : Algebra.Etale (Localization.Away f) R')
    (_ : Module.FaithfullyFlat (Localization.Away f) R')
    (B : Fin M → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra (Localization.Away f) (B i))
    (_ : ∀ i, Module.Finite (Localization.Away f) (B i)) (_ : ∀ i, Algebra.Etale (Localization.Away f) (B i))
    (deg : Fin M → ℕ) (_ : ∀ i, 1 ≤ deg i) (_ : ∀ i, deg i ≤ b)
    (_φ : ∀ i, TensorProduct (Localization.Away f) R' (B i) ≃ₐ[R'] (Fin (deg i) → R'))
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f)))
    (_ : ∀ i, IsClosedImmersion (z i)),
    (∀ i, z i ≫ baseChange ℤ (DRModel.toBase p) (Localization.Away f) = specMap (Localization.Away f) (B i)) ∧
    (∀ i, Set.range (z i).base ⊆
      ((pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f)) ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f))).Opens) :
        Set ↥(pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f))))) ∧
    (Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base)) ∧
    (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
      (i : Fin M),
      (pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).base ⁻¹' Set.range (z i).base ⊆
        connectedComponentIn
          (((pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s ≫ pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
              (pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s))
          (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k))) := by sorry
