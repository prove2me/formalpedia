-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_exists_locallySplitPools_of_five_le
-- name    : ModularCurve.DRModelPackage.exists_locallySplitPools_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/978af290-8da4-5a9a-8d48-abe1b100eff8
-- title:
--   Local pools of disjoint étale multisections near the cusp
-- statement:
--   Let $p$ be a prime with $5 \le p$, and let $\mathfrak{X}$ be a `DRModelPackage p`, i.e. a bundle of data for the two-chart integral model `DRModel p` of the full level-$p$ modular function field over $\mathbb{Z}$: properness, flatness and integrality of the structure morphism `DRModel.toBase p`, integral closedness of the sections over affine opens, curve models of the generic fibre over $\mathbb{Q}$ and over $\overline{\mathbb{Q}}$ with their Galois and place compatibilities, two sections $\varepsilon_\infty, \varepsilon_0$ of `DRModel.toBase p`, and a distinguished open `smoothLocus`, smooth of relative dimension $1$ over $\mathbb{Z}$ and maximal among such opens. The assertion is that for every prime $\mathfrak{p}$ of $\mathbb{Z}$ and all natural numbers $A_0, B_0, n_0$ there are: an $f \in \mathbb{Z}$ with $f \notin \mathfrak{p}$; natural numbers $b$ and $M$ with $A_0 b^{n_0} + B_0 < M$; a ring $R'$, an algebra over $\mathbb{Z}$ and over $L := \mathbb{Z}[1/f] =$ `Localization.Away f` compatibly, finite, étale and faithfully flat over $L$; a family $B : \mathrm{Fin}\,M \to \mathrm{Type}$ of finite étale $L$-algebras; degrees $\deg i$ with $1 \le \deg i \le b$; $R'$-algebra isomorphisms $R' \otimes_L B_i \cong R'^{\deg i}$; and closed immersions $z_i : \operatorname{Spec} B_i \to \mathfrak{X}_L := \mathrm{DRModel}(p) \times_{\operatorname{Spec}\mathbb{Z}} \operatorname{Spec} L$, such that (i) $z_i$ followed by the projection $\mathfrak{X}_L \to \operatorname{Spec} L$ is $\operatorname{Spec}$ of the structure map $L \to B_i$; (ii) the image of each $z_i$ lies in the preimage of $\mathfrak{X}.\mathrm{smoothLocus}$ under the first projection; (iii) the images of the $z_i$ are pairwise disjoint; and (iv) for every algebraically closed field $k$, every $s : \operatorname{Spec} k \to \operatorname{Spec} L$ and every $i$, the preimage in the fibre $\mathfrak{X}_L \times_{\operatorname{Spec} L} \operatorname{Spec} k$ of the image of $z_i$ is contained in the connected component, within the preimage of $\mathfrak{X}.\mathrm{smoothLocus}$ in that fibre, of the point cut out by the base change of the section $\varepsilon_\infty$ to $L$ and then to $s$, evaluated at the closed point of $\operatorname{Spec} k$.
--
--   This supplies the pools of disjoint finite étale multisections, lying in the smooth locus and in the cusp component of every geometric fibre, that are required as input data for the second leg of the argument; it is the `hpool` component consumed by [`ModularCurve.nonempty_legTwoInputV2`](thm.html#ModularCurve.nonempty_legTwoInputV2). The numerical shape $A_0 b^{n_0} + B_0 < M$ allows the number of multisections to be prescribed in advance in terms of the degree bound $b$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_exists_locallySplitPools_of_five_le.lean

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

theorem ModularCurve.DRModelPackage.exists_locallySplitPools_of_five_le
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p) : ∀ (𝔭 : PrimeSpectrum ℤ) (A₀ B₀ n₀ : ℕ), ∃ (f : ℤ) (_ : f ∉ 𝔭.asIdeal) (b M : ℕ) (_ : A₀ * b ^ n₀ + B₀ < M)
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
