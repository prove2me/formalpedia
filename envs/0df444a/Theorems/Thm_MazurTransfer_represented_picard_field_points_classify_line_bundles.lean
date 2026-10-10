-- Prove2me | Theorems.Thm_MazurTransfer_represented_picard_field_points_classify_line_bundles
-- name    : MazurTransfer.represented_picard_field_points_classify_line_bundles
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-09T21:49:19.679756+00:00
-- url     : https://prove2.me/theorems/4a1681d5-ba42-44e4-bab6-ab511ea83079
-- title:
--   Every represented Picard scheme classifies degree-zero line bundles over the base field
-- statement:
--   Let $X$ be a proper, smooth, geometrically integral curve over a field $K$, with a rational rigidifying section $\varepsilon$. Let $D$ be any scheme representing its degree-zero relative Picard functor, and let $M_a$ be the actual line bundle on $X$ obtained by pulling its Poincaré bundle back at $a\in D(K)$. Then $M_a$ is invertible with $\chi_K(M_a)=\chi_K(\mathcal O_X)$, and
--   \[
--   M_a\simeq M_b\quad\Longleftrightarrow\quad a=b.
--   \]
--   Conversely, every invertible line bundle $N$ with $\chi_K(N)=\chi_K(\mathcal O_X)$ is isomorphic to $M_a$ for a unique $a\in D(K)$. Euler characteristics are computed over $K$ itself using the given two-affine-open cover. The base field need not be algebraically closed. This applies to every representing designation, providing the classification needed in the arithmetic divisor-class/Picard-point group correspondence.
-- source:
--   Vas and contributors, MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0, https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Official Anthropic FLT Picard and cohomology infrastructure at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0, https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . Generic field argument reuses our full-source audited classification proof accepted as 47b952a2-90f7-443d-87bc-2be4e9f2eced, retaining actual Poincare pullbacks and arbitrary representing designations.

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian

theorem MazurTransfer.represented_picard_field_points_classify_line_bundles.{u}
    {K : Type u} [Field K] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of K))
    [IsProper x] [SmoothOfRelativeDimension 1 x] [GeometricallyIntegral x]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) x)
    (D : RelativePic0Designation K x)
    (h : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D) :
      let M := fun a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase =>
        (Scheme.Modules.pullback
          (toProdSpec (x))).obj
          (h.poincare.pullbackAlong a).L
      (∀ a, Scheme.Modules.IsInvertible (M a) ∧
        ∀ 𝒱 : (X).TwoAffineOpenCover,
          (Module.finrank K
            (𝒱.sectionsOf (x) (M a)).H0 : ℤ) -
            Module.finrank K
              (𝒱.sectionsOf (x) (M a)).H1 =
          (Module.finrank K
            (𝒱.sectionsOf (x)
              (𝟙_ (X).Modules)).H0 : ℤ) -
            Module.finrank K
              (𝒱.sectionsOf (x)
                (𝟙_ (X).Modules)).H1) ∧
      (∀ a b, Nonempty (M a ≅ M b) ↔ a = b) ∧
      (∀ (𝒱 : (X).TwoAffineOpenCover)
        (N : (X).Modules),
        Scheme.Modules.IsInvertible N →
        (Module.finrank K
          (𝒱.sectionsOf (x) N).H0 : ℤ) -
          Module.finrank K
            (𝒱.sectionsOf (x) N).H1 =
        (Module.finrank K
          (𝒱.sectionsOf (x)
            (𝟙_ (X).Modules)).H0 : ℤ) -
          Module.finrank K
            (𝒱.sectionsOf (x)
              (𝟙_ (X).Modules)).H1 →
        ∃! a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase,
          Nonempty (M a ≅ N)) := by sorry
