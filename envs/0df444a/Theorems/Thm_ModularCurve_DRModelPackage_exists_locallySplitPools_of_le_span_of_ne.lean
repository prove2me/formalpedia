-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_exists_locallySplitPools_of_le_span_of_ne
-- name    : ModularCurve.DRModelPackage.exists_locallySplitPools_of_le_span_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/3fa16bb6-a0fd-56b6-9d57-5ab8f625888a
-- title:
--   Locally split pools at primes 𝔭⊆(ℓ), ℓ≠ p
-- statement:
--   Let $p$ be a prime, let $\mathfrak X$ be a `DRModelPackage p`, i.e. the two-chart integral model `DRModel p` of the full modular function field at level $p$ over $\operatorname{Spec}\mathbb Z$ together with its properness, flatness, integrality and normality data, its generic-fibre curve models over $\mathbb Q$ and over $\overline{\mathbb Q}$ with their Galois compatibilities, its two sections $\varepsilon_\infty,\varepsilon_0$ and its distinguished open `smoothLocus`. Let $\mathfrak p$ be a prime of $\mathbb Z$, let $A_0,B_0,n_0$ be naturals, and let $\ell$ be a prime with $\ell\neq p$ and $\mathfrak p\subseteq(\ell)$. Then there are $f\in\mathbb Z\setminus\mathfrak p$, naturals $b,M$ with $A_0b^{n_0}+B_0<M$, a commutative ring $R'$ carrying compatible $\mathbb Z$- and $\mathbb Z[1/f]=$ `Localization.Away f`-algebra structures and finite, étale and faithfully flat over $\mathbb Z[1/f]$, rings $B_i$ ($i\in\operatorname{Fin} M$) finite étale over $\mathbb Z[1/f]$, degrees $1\le \deg i\le b$ with $R'$-algebra isomorphisms $R'\otimes_{\mathbb Z[1/f]}B_i\cong R'^{\deg i}$, and closed immersions $z_i\colon\operatorname{Spec}B_i\to \mathfrak X\times_{\operatorname{Spec}\mathbb Z}\operatorname{Spec}\mathbb Z[1/f]$ such that: each $z_i$ followed by the projection to $\operatorname{Spec}\mathbb Z[1/f]$ is $\operatorname{Spec}$ of the structure map $\mathbb Z[1/f]\to B_i$; each image lies in the preimage of `𝔛.smoothLocus` under the first projection; the images are pairwise disjoint; and for every algebraically closed field $k$, every $s\colon\operatorname{Spec}k\to\operatorname{Spec}\mathbb Z[1/f]$ and every $i$, the preimage of the image of $z_i$ in the fibre over $s$ lies in the connected component, inside the preimage of `𝔛.smoothLocus` in that fibre, of the point cut out by the base change of $\varepsilon_\infty$ at $s$.
--
--   This provides the pools of auxiliary, pairwise disjoint, generically split finite étale points in the smooth locus of the Deligne–Rapoport model that lie in the same geometric connected component as the cusp $\infty$; it is the case of residue characteristics $\ell\neq p$ (including the generic point $\mathfrak p=(0)$), where the model has good reduction and the pools can be taken to be level sets of the $j$-function on the finite chart. It is one of the two inputs to [`ModularCurve.DRModelPackage.exists_locallySplitPools_of_five_le`](thm.html#ModularCurve.DRModelPackage.exists_locallySplitPools_of_five_le), which assembles the pools over all primes of $\mathbb Z$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_exists_locallySplitPools_of_le_span_of_ne.lean

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

theorem ModularCurve.DRModelPackage.exists_locallySplitPools_of_le_span_of_ne
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (𝔭 : PrimeSpectrum ℤ) (A₀ B₀ n₀ : ℕ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (h𝔭ℓ : 𝔭.asIdeal ≤ Ideal.span {(ℓ : ℤ)}) :
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
