-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_twoGluedSmoothCurveDegenerations
-- name    : ModularCurve.DRModelPackageLevel.twoGluedSmoothCurveDegenerations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/7a22f891-993f-5360-906f-99a844c25245
-- title:
--   Non-smooth fibres of the Deligne–Rapoport model are two glued curves
-- statement:
--   Fix $N_0 \ge 1$ and a prime $q$ with $q \nmid N_0$, and let $\mathfrak P$ be a `DRModelPackageLevel` for these data: a bundle consisting of the proper, flat, integral, locally finitely presented structure morphism `DRLevel.toBase N₀ q` of the Igusa-type model of level $N_0q$ over $\operatorname{Spec}(R q)$, normality of its affine sections, an identification of its geometric generic fibre with a curve model of the modular function field compatible with the Galois action and with the $q$-expansion charts, smoothness of relative dimension $1$ and geometric integrality of the fibre over $\mathbb Q$, sections $\varepsilon_\infty$, $\varepsilon_0$ of the structure morphism, and an open smooth locus $\mathfrak P.\mathtt{smoothLocus}$, among further data. The assertion is that for every algebraically closed field $k$ and every $s\colon\operatorname{Spec} k \to \operatorname{Spec}(R q)$ such that the base-changed morphism $\mathfrak X_s := \mathfrak X\times_{\operatorname{Spec}(Rq)}\operatorname{Spec} k \to \operatorname{Spec} k$ (the second projection) fails to be smooth, there exist $k$-schemes $C_1, C_2$ with structure morphisms $c_1, c_2$ that are proper, smooth of relative dimension $1$ and geometrically integral, morphisms $i_1, i_2$ of $C_1, C_2$ into $\mathfrak X_s$ commuting with the structure morphisms over $\operatorname{Spec} k$, both closed immersions, and a natural number $n$, with the following properties. Every point of $\mathfrak X_s$ lies in the image of $i_1$ or of $i_2$; the scheme-theoretic intersection $C_1\times_{\mathfrak X_s}C_2$ is reduced and has exactly $n$ points, with $n>0$; the $k$-point of $\mathfrak X_s$ obtained from the section $\varepsilon_\infty$ by base change along $s$ (the image of the closed point of $\operatorname{Spec} k$) lies in the image of $i_1$ but not in that of $i_2$; writing $U_s$ for the preimage of $\mathfrak P.\mathtt{smoothLocus}$ under the first projection $\mathfrak X_s \to \mathfrak X$, the underlying set of $U_s$ is the complement of the image of $C_1\times_{\mathfrak X_s}C_2$ in $\mathfrak X_s$ (via the first projection followed by $i_1$); the intersection of the image of $i_1$ with $U_s$ is the connected component of the cusp point in $U_s$, and the intersection of the image of $i_2$ with $U_s$ is the complement in $U_s$ of that connected component; finally there are opens $W_1, W_2$ of $\mathfrak X_s$ whose underlying sets are the complements of the images of $i_2$ and of $i_1$ respectively, such that the inclusion of $i_1^{-1}(W_1)$ followed by $i_1$, and the inclusion of $i_2^{-1}(W_2)$ followed by $i_2$, are open immersions.
--
--   This is the Deligne–Rapoport description of a bad geometric fibre of the modular curve of level $N_0q$ at the prime $q$ dividing the level exactly once: two smooth proper geometrically integral curves meeting in finitely many, at least one, points, the cusp $\infty$ lying on the first one only, with the smooth locus of the fibre being the complement of the crossing points and the two components meeting it in the component of $\infty$ and its complement. It supplies the degeneration hypothesis for the representability statement [`ModularCurve.DRModelPackageLevel.exists_representsRelSubPic`](thm.html#ModularCurve.DRModelPackageLevel.exists_representsRelSubPic) about the relative Picard functor of the model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_twoGluedSmoothCurveDegenerations.lean

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
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve

theorem ModularCurve.DRModelPackageLevel.twoGluedSmoothCurveDegenerations
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN) :
    ∀ (k : Type) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (DRLevel.R q))), ¬ Smooth (pullback.snd (DRLevel.toBase N₀ q) s) →
      ∃ (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
        (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
        (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
        (i₁ : SchemeHomOver c₁ (pullback.snd (DRLevel.toBase N₀ q) s)) (i₂ : SchemeHomOver c₂ (pullback.snd (DRLevel.toBase N₀ q) s))
        (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ),
        (∀ z : ↥(pullback (DRLevel.toBase N₀ q) s), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n ∧
        ((sectionFibrePoint 𝔓.εinf s).1).base (IsLocalRing.closedPoint k) ∈ Set.range i₁.1.base \ Set.range i₂.1.base ∧
        ((pullback.fst (DRLevel.toBase N₀ q) s ⁻¹ᵁ 𝔓.smoothLocus : (pullback (DRLevel.toBase N₀ q) s).Opens) : Set ↥(pullback (DRLevel.toBase N₀ q) s)) =
          (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ ∧
        Set.range i₁.1.base ∩ ((pullback.fst (DRLevel.toBase N₀ q) s ⁻¹ᵁ 𝔓.smoothLocus : (pullback (DRLevel.toBase N₀ q) s).Opens) : Set ↥(pullback (DRLevel.toBase N₀ q) s)) =
          connectedComponentIn ((pullback.fst (DRLevel.toBase N₀ q) s ⁻¹ᵁ 𝔓.smoothLocus : (pullback (DRLevel.toBase N₀ q) s).Opens) : Set ↥(pullback (DRLevel.toBase N₀ q) s))
            (((sectionFibrePoint 𝔓.εinf s).1).base (IsLocalRing.closedPoint k)) ∧
        Set.range i₂.1.base ∩ ((pullback.fst (DRLevel.toBase N₀ q) s ⁻¹ᵁ 𝔓.smoothLocus : (pullback (DRLevel.toBase N₀ q) s).Opens) : Set ↥(pullback (DRLevel.toBase N₀ q) s)) =
          ((pullback.fst (DRLevel.toBase N₀ q) s ⁻¹ᵁ 𝔓.smoothLocus : (pullback (DRLevel.toBase N₀ q) s).Opens) : Set ↥(pullback (DRLevel.toBase N₀ q) s)) \
            connectedComponentIn ((pullback.fst (DRLevel.toBase N₀ q) s ⁻¹ᵁ 𝔓.smoothLocus : (pullback (DRLevel.toBase N₀ q) s).Opens) : Set ↥(pullback (DRLevel.toBase N₀ q) s))
              (((sectionFibrePoint 𝔓.εinf s).1).base (IsLocalRing.closedPoint k)) ∧
        (∃ W₁ : (pullback (DRLevel.toBase N₀ q) s).Opens, (W₁ : Set ↥(pullback (DRLevel.toBase N₀ q) s)) = (Set.range i₂.1.base)ᶜ ∧
          IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1)) ∧
        (∃ W₂ : (pullback (DRLevel.toBase N₀ q) s).Opens, (W₂ : Set ↥(pullback (DRLevel.toBase N₀ q) s)) = (Set.range i₁.1.base)ᶜ ∧
          IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1)) := by sorry
