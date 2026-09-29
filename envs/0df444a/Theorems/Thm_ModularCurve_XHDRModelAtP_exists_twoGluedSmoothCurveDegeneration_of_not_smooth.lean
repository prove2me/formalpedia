-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_twoGluedSmoothCurveDegeneration_of_not_smooth
-- name    : ModularCurve.XHDRModelAtP.exists_twoGluedSmoothCurveDegeneration_of_not_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/5bae9043-5a42-51f1-ad27-a48db0b0dba2
-- title:
--   Two glued smooth curves in non-smooth fibres of X_H(M)
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$ but $p^{2} \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and the hypothesis $hj$ that the Laurent series $jqModC$ over $\mathbb{Q}$ lies in the field $qExpFunctionFieldC$ of $q$-expansions at level $SL(2,\mathbb{Z})$; let $\mathfrak{X}$ be an `XHDRModelAtP` datum for these, so in particular the two-chart integral model $c :=$ `toBase p (ΓM M H) hj` of the level-$\Gamma_H(M)$ function field over $\operatorname{Spec} R_p$ is proper, flat, integral and locally of finite presentation, with a distinguished open $\mathfrak{X}.smoothLocus$ and a section $\mathfrak{X}.\varepsilon_{\infty}$ of $c$. The assertion: for every algebraically closed field $k$ and every $s : \operatorname{Spec} k \to \operatorname{Spec} R_p$ such that the fibre $c_s$, i.e. the second projection of $\operatorname{pullback}(c,s)$, is not smooth, there are $k$-schemes $C_1, C_2$, each proper, smooth of relative dimension $1$ and geometrically integral over $k$, closed immersions $i_1 : C_1 \to \operatorname{pullback}(c,s)$ and $i_2 : C_2 \to \operatorname{pullback}(c,s)$ compatible with the structure maps to $\operatorname{Spec} k$, and $n \in \mathbb{N}$, such that: every point of the fibre lies in the image of $i_1$ or of $i_2$; the scheme-theoretic intersection $\operatorname{pullback}(i_1,i_2)$ is reduced with exactly $n$ points and $n > 0$; the $k$-point of the fibre obtained from $\mathfrak{X}.\varepsilon_{\infty}$ via `sectionFibrePoint`, evaluated at the closed point of $\operatorname{Spec} k$, lies in the image of $i_1$ but not of $i_2$; the preimage of $\mathfrak{X}.smoothLocus$ under the first projection equals the complement of the image of the intersection; inside that preimage, the image of $i_1$ cuts out exactly the connected component of the $\varepsilon_{\infty}$-point and the image of $i_2$ cuts out its complement; and there are opens $W_1, W_2$ of the fibre with underlying sets the complements of the images of $i_2$, respectively $i_1$, such that the inclusion of $i_1^{-1}W_1$ followed by $i_1$, and the inclusion of $i_2^{-1}W_2$ followed by $i_2$, are open immersions.
--
--   This is the Deligne–Rapoport description of the bad geometric fibres of the modular curve $X_H(M)$ at a prime exactly dividing the level: such a fibre is the union of two smooth proper geometrically integral curves meeting in a finite non-empty reduced set (the supersingular points), the cuspidal section $\varepsilon_\infty$ lying on the first component, with the smooth locus of the model recovering exactly the complement of the crossing points. It is packaged here in the shape required by the general two-glued-curves input to relative Picard computations, and is used by the results on representability of the relative sub-Picard functor and on the fibres of the $\varepsilon_\infty$-cut.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_twoGluedSmoothCurveDegeneration_of_not_smooth.lean

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

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve ModularCurve.XHDRLevel
open AlgebraicGeometry
open AlgebraicGeometry.RelPicard

open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_twoGluedSmoothCurveDegeneration_of_not_smooth
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj) :
    ∀ (k : Type) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (R p))), ¬ Smooth (pullback.snd (toBase p (ΓM M H) hj) s) →
      ∃ (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
        (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
        (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
        (i₁ : SchemeHomOver c₁ (pullback.snd (toBase p (ΓM M H) hj) s)) (i₂ : SchemeHomOver c₂ (pullback.snd (toBase p (ΓM M H) hj) s))
        (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ),
        (∀ z : ↥(pullback (toBase p (ΓM M H) hj) s), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n ∧
        ((sectionFibrePoint 𝔛.εinf s).1).base (IsLocalRing.closedPoint k) ∈ Set.range i₁.1.base \ Set.range i₂.1.base ∧
        ((pullback.fst (toBase p (ΓM M H) hj) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (toBase p (ΓM M H) hj) s).Opens) : Set ↥(pullback (toBase p (ΓM M H) hj) s)) =
          (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ ∧
        Set.range i₁.1.base ∩ ((pullback.fst (toBase p (ΓM M H) hj) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (toBase p (ΓM M H) hj) s).Opens) : Set ↥(pullback (toBase p (ΓM M H) hj) s)) =
          connectedComponentIn ((pullback.fst (toBase p (ΓM M H) hj) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (toBase p (ΓM M H) hj) s).Opens) : Set ↥(pullback (toBase p (ΓM M H) hj) s))
            (((sectionFibrePoint 𝔛.εinf s).1).base (IsLocalRing.closedPoint k)) ∧
        Set.range i₂.1.base ∩ ((pullback.fst (toBase p (ΓM M H) hj) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (toBase p (ΓM M H) hj) s).Opens) : Set ↥(pullback (toBase p (ΓM M H) hj) s)) =
          ((pullback.fst (toBase p (ΓM M H) hj) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (toBase p (ΓM M H) hj) s).Opens) : Set ↥(pullback (toBase p (ΓM M H) hj) s)) \
            connectedComponentIn ((pullback.fst (toBase p (ΓM M H) hj) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (toBase p (ΓM M H) hj) s).Opens) : Set ↥(pullback (toBase p (ΓM M H) hj) s))
              (((sectionFibrePoint 𝔛.εinf s).1).base (IsLocalRing.closedPoint k)) ∧
        (∃ W₁ : (pullback (toBase p (ΓM M H) hj) s).Opens, (W₁ : Set ↥(pullback (toBase p (ΓM M H) hj) s)) = (Set.range i₂.1.base)ᶜ ∧
          IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1)) ∧
        (∃ W₂ : (pullback (toBase p (ΓM M H) hj) s).Opens, (W₂ : Set ↥(pullback (toBase p (ΓM M H) hj) s)) = (Set.range i₁.1.base)ᶜ ∧
          IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1)) := by sorry
