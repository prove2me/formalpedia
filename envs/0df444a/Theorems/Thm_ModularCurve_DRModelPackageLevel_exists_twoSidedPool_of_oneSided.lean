-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_twoSidedPool_of_oneSided
-- name    : ModularCurve.DRModelPackageLevel.exists_twoSidedPool_of_oneSided
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/7816743a-a36e-5c91-9ed1-a067ea7eeb76
-- title:
--   Two-sided pools from one-sided pools via the involution w
-- statement:
--   Fix $N_0$ with $N_0\neq 0$ and a prime $q$ with $q\nmid N_0$, and let $\mathfrak P$ be a package `DRModelPackageLevel N₀ q hqN` for the model `toBase N₀ q : X N₀ q ⟶ Spec (R q)` of level $N_0q$ at $q$ over the base ring `R q`. Among the data of $\mathfrak P$ the following are used: an open subscheme `𝔓.smoothLocus` of `X N₀ q`, two sections `𝔓.εinf` and `𝔓.εzero` of `toBase N₀ q` over the identity of $\operatorname{Spec}(R q)$, and an endomorphism `𝔓.w.hom` of `X N₀ q` together with the witness `𝔓.w_over` that it lies over the base.
--
--   Natural numbers $A_0$, $B_0$, $n_0$ and an element $f$ of `R q` are fixed; write $L$ for `Localization.Away f`, $\mathfrak X_L$ for the pullback of `toBase N₀ q` along `specMap (R q) L`, with first projection $p\colon\mathfrak X_L\to$ `X N₀ q` and structure morphism `baseChange (R q) (toBase N₀ q) L` $\colon\mathfrak X_L\to\operatorname{Spec}L$, and $U_L=p^{-1}(\mathfrak P.\mathrm{smoothLocus})$, an open of $\mathfrak X_L$. Let $w_L$ denote `curveChange 𝔓.w.hom 𝔓.w_over (specMap (R q) L)`, the induced endomorphism of $\mathfrak X_L$. For an algebraically closed field $k$ and a morphism $s\colon\operatorname{Spec}k\to\operatorname{Spec}L$, write $\mathfrak X_s$ for the pullback of `baseChange (R q) (toBase N₀ q) L` along $s$, with projections $\pi\colon\mathfrak X_s\to\mathfrak X_L$ and $\mathfrak X_s\to\operatorname{Spec}k$; put $U_s=(\pi\mathbin{;}p)^{-1}(\mathfrak P.\mathrm{smoothLocus})$, let $P_\infty(s)$ be the image of the closed point of $\operatorname{Spec}k$ under `sectionFibrePoint (sectionBaseChange L 𝔓.εinf) s`, let $P_0(s)$ be the corresponding point for `𝔓.εzero`, and let $C_\infty(s)=$ `connectedComponentIn` $U_s\,P_\infty(s)$ be the connected component of $P_\infty(s)$ inside the subspace $U_s$ (empty if $P_\infty(s)\notin U_s$).
--
--   The far-side hypothesis `hfar` states: for every algebraically closed field $k$ and every $s\colon\operatorname{Spec}k\to\operatorname{Spec}L$ such that the fibre morphism `pullback.snd (baseChange (R q) (toBase N₀ q) L) s` $\colon\mathfrak X_s\to\operatorname{Spec}k$ is not smooth, both (i) every point $y$ of $\mathfrak X_s$ lying in $C_\infty(s)$ has its image under the endomorphism of $\mathfrak X_s$ induced by $w_L$ (the pullback map with components $w_L$ and the identity) in $U_s\setminus C_\infty(s)$, and (ii) $P_0(s)\in U_s\setminus C_\infty(s)$.
--
--   The one-sided pool data consist of: natural numbers $b$ and $M$ with `hM` $\colon A_0b^{n_0}+B_0<M$; a commutative ring $R'$ which is an algebra over `R q` and over $L$, compatibly, and which is finite, étale and faithfully flat over $L$; a family $B\colon\mathrm{Fin}\,M\to\mathrm{Type}$ of commutative rings, each a finite étale $L$-algebra; degrees $\deg\colon\mathrm{Fin}\,M\to\mathbb N$ with `hdeg` $\colon 1\le\deg i$ and `hdegb` $\colon\deg i\le b$ for all $i$; $R'$-algebra isomorphisms $\varphi_i\colon R'\otimes_L B_i\simeq R'^{\deg i}$; and morphisms $z_i\colon\operatorname{Spec}B_i\to\mathfrak X_L$, each a closed immersion. They are required to satisfy: `hz₁`, that $z_i$ followed by `baseChange (R q) (toBase N₀ q) L` equals `specMap L (B i)`, i.e. $z_i$ is a closed immersion over $\operatorname{Spec}L$; `hz₂`, that the range of $z_i$ on points is contained in $U_L$; `hz₃`, that the ranges of $z_i$ and $z_j$ are disjoint for $i\neq j$; and `hz₄`, that for every algebraically closed field $k$, every $s\colon\operatorname{Spec}k\to\operatorname{Spec}L$ (no smoothness assumption on the fibre) and every $i$, the preimage under $\pi$ of the range of $z_i$ is contained in $C_\infty(s)$.
--
--   Three cross-disjointness hypotheses are imposed: `hzinf`, the range of each $z_i$ is disjoint from the range of `sectionBaseChange L 𝔓.εinf`; `hzzero`, likewise disjoint from the range of `sectionBaseChange L 𝔓.εzero`; and `hzw`, for all $i,j$ the range of $z_i$ is disjoint from the range of $z_j$ followed by $w_L$.
--
--   Under these hypotheses there exist natural numbers $b$, $M$, $M'$ (the names $b$, $M$, $R'$, $B$, $\deg$, $\varphi$, $z$ are re-bound in the conclusion) with $A_0b^{n_0}+B_0<M$ and $A_0b^{n_0}+B_0<M'$; a commutative ring $R'$ with algebra structures over `R q` and over $L$, compatible, and finite, étale and faithfully flat over $L$; a family $B\colon\mathrm{Fin}\,M\to\mathrm{Type}$ of commutative rings, each finite étale over $L$, degrees $\deg$ with $1\le\deg i\le b$, isomorphisms $\varphi_i\colon R'\otimes_L B_i\simeq R'^{\deg i}$ of $R'$-algebras and closed immersions $z_i\colon\operatorname{Spec}B_i\to\mathfrak X_L$; and a second family $B'\colon\mathrm{Fin}\,M'\to\mathrm{Type}$ of commutative rings, each finite étale over $L$, degrees $\deg'$ with $1\le\deg' i\le b$, isomorphisms $\varphi'_i\colon R'\otimes_L B'_i\simeq R'^{\deg' i}$ and closed immersions $z'_i\colon\operatorname{Spec}B'_i\to\mathfrak X_L$ (all ring, algebra, finiteness, étaleness and faithful flatness structures being part of the existential statement), such that the following ten conditions hold:
--
--   (1) each $z_i$ followed by `baseChange (R q) (toBase N₀ q) L` equals `specMap L (B i)`; (2) the range of each $z_i$ lies in $U_L$; (3) the ranges of the $z_i$ are pairwise disjoint; (4) for every algebraically closed field $k$, every $s\colon\operatorname{Spec}k\to\operatorname{Spec}L$ and every $i<M$, the preimage under $\pi$ of the range of $z_i$ is contained in $C_\infty(s)$; (5) there is an index $j$ with $\deg' j\le 1$ (hence, with $1\le\deg' j$, equal to $1$); (6) each $z'_i$ followed by `baseChange (R q) (toBase N₀ q) L` equals `specMap L (B' i)`; (7) the range of each $z'_i$ lies in $U_L$; (8) the ranges of the $z'_i$ are pairwise disjoint; (9) the range of $z_i$ is disjoint from the range of $z'_j$ for all $i$ and $j$; (10) for every algebraically closed field $k$, every $s\colon\operatorname{Spec}k\to\operatorname{Spec}L$ and every $i<M'$, if the fibre morphism $\mathfrak X_s\to\operatorname{Spec}k$ is not smooth then the preimage under $\pi$ of the range of $z'_i$ is contained in $U_s\setminus C_\infty(s)$.
--
--   Thus the conclusion asserts nothing about disjointness of the far family from the two cusp sections or about $w_L$-translates, and its far-side condition (10) is only imposed at non-smooth geometric fibres.
--
--   This is the passage from a one-sided pool of étale multisections concentrated in the component $C_\infty$ of the smooth locus to a two-sided pool, the far half being produced by transport along the involution $w$ of the model together with the degree-one section `𝔓.εzero`. It is the common generic step of the three closed-prime pool statements `exists_twoSidedPool_smoothLocus_closedPrime_of_five_le`, `exists_twoSidedPool_smoothLocus_closedPrime_three` and `exists_twoSidedPool_smoothLocus_closedPrime_two` in the construction of the relative Picard functor of the Deligne–Rapoport model of $X_0(N_0q)$ over `R q`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_twoSidedPool_of_oneSided.lean

import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelPicardPullback

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

theorem exists_twoSidedPool_of_oneSided (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (A₀ B₀ n₀ : ℕ) (f : R q)
    (hfar : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f))),
      ¬ Smooth (pullback.snd (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s) →
      (∀ y : ↥(pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s),
        y ∈ connectedComponentIn
            (((pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s ≫ pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))) ⁻¹ᵁ 𝔓.smoothLocus :
                (pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔓.εinf) s).1).base (IsLocalRing.closedPoint k)) →
        (pullback.map (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s
            (curveChange 𝔓.w.hom 𝔓.w_over (specMap (R q) (Localization.Away f))) (𝟙 _) (𝟙 _)
            ((Category.comp_id _).trans (curveChange_snd _ _ _).symm)
            ((Category.comp_id _).trans (Category.id_comp _).symm)).base y ∈
          (((pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s ≫ pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))) ⁻¹ᵁ 𝔓.smoothLocus :
                (pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s)) \
          connectedComponentIn
            (((pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s ≫ pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))) ⁻¹ᵁ 𝔓.smoothLocus :
                (pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔓.εinf) s).1).base (IsLocalRing.closedPoint k))) ∧
      ((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔓.εzero) s).1).base (IsLocalRing.closedPoint k) ∈
          (((pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s ≫ pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))) ⁻¹ᵁ 𝔓.smoothLocus :
                (pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s)) \
          connectedComponentIn
            (((pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s ≫ pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))) ⁻¹ᵁ 𝔓.smoothLocus :
                (pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔓.εinf) s).1).base (IsLocalRing.closedPoint k)))
    (b M : ℕ) (hM : A₀ * b ^ n₀ + B₀ < M)
    (R' : Type) [CommRing R'] [Algebra (R q) R'] [Algebra (Localization.Away f) R'] [IsScalarTower (R q) (Localization.Away f) R']
    [Module.Finite (Localization.Away f) R'] [Algebra.Etale (Localization.Away f) R'] [Module.FaithfullyFlat (Localization.Away f) R']
    (B : Fin M → Type) [∀ i, CommRing (B i)] [∀ i, Algebra (Localization.Away f) (B i)]
    [∀ i, Module.Finite (Localization.Away f) (B i)] [∀ i, Algebra.Etale (Localization.Away f) (B i)]
    (deg : Fin M → ℕ) (hdeg : ∀ i, 1 ≤ deg i) (hdegb : ∀ i, deg i ≤ b)
    (φ : ∀ i, TensorProduct (Localization.Away f) R' (B i) ≃ₐ[R'] (Fin (deg i) → R'))
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback (toBase N₀ q) (specMap (R q) (Localization.Away f)))
    [∀ i, IsClosedImmersion (z i)]
    (hz₁ : ∀ i, z i ≫ baseChange (R q) (toBase N₀ q) (Localization.Away f) = specMap (Localization.Away f) (B i))
    (hz₂ : ∀ i, Set.range (z i).base ⊆
      ((pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f)) ⁻¹ᵁ 𝔓.smoothLocus : (pullback (toBase N₀ q) (specMap (R q) (Localization.Away f))).Opens) :
        Set ↥(pullback (toBase N₀ q) (specMap (R q) (Localization.Away f)))))
    (hz₃ : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    (hz₄ : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
      (i : Fin M),
      (pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).base ⁻¹' Set.range (z i).base ⊆
        connectedComponentIn
          (((pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s ≫ pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))) ⁻¹ᵁ 𝔓.smoothLocus :
              (pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s))
          (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔓.εinf) s).1).base (IsLocalRing.closedPoint k)))
    (hzinf : ∀ i, Disjoint (Set.range (z i).base) (Set.range (sectionBaseChange (Localization.Away f) 𝔓.εinf).1.base))
    (hzzero : ∀ i, Disjoint (Set.range (z i).base) (Set.range (sectionBaseChange (Localization.Away f) 𝔓.εzero).1.base))
    (hzw : ∀ i j, Disjoint (Set.range (z i).base)
      (Set.range (z j ≫ curveChange 𝔓.w.hom 𝔓.w_over (specMap (R q) (Localization.Away f))).base)) :
    ∃ (b M M' : ℕ)
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
