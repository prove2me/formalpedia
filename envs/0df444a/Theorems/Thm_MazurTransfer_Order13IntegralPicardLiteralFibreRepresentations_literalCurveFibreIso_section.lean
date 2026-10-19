-- Prove2me | Theorems.Thm_MazurTransfer_Order13IntegralPicardLiteralFibreRepresentations_literalCurveFibreIso_section
-- name    : MazurTransfer.Order13IntegralPicardLiteralFibreRepresentations.literalCurveFibreIso_section
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T04:20:22.894992+00:00
-- url     : https://prove2.me/theorems/d0a03b5e-be40-40f7-adf7-2c35307bdf2a
-- title:
--   The actual literal fibre isomorphism preserves the positive infinity section
-- statement:
--   Let $R$ and $S$ be commutative rings with an $R$-algebra structure on $S$. Let $e_{S/R}:C_S\to C_R\times_{\operatorname{Spec}R}\operatorname{Spec}S$ be the specified actual fibre isomorphism, and let $\infty_R^+$ and $\infty_S^+$ be the actual positive infinity sections. Then
--   $$e_{S/R}\circ\infty_S^+=(\infty_R^+)_S,$$
--   where $(\infty_R^+)_S$ is the base-changed section.
--
--   This supplies the distinguished-section compatibility needed to transport the integral Picard representation to the literal new-base curve and to read the Abel–Jacobi point-difference dictionary on that curve.
-- source:
--   Unchanged statement and target proof from the checked MazurTheorem Order13IntegralPicardLiteralFibreRepresentations.lean, literalCurveFibreIso_section. Exact Lean syntax-oracle ranges hoist the solution with its section binders. The proof uses the public actual Cartesian square, literal fibre isomorphism, and infinity-morphism naturality theorem. The full original and public types are checked by closed kernel witnesses. Vas and contributors, Apache-2.0.

import Mathlib
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_MazurTransfer_Order13IntegralInfinitySections
import Definitions.Def_MazurTransfer_Order13LiteralCurveFibreIsomorphism
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve
open MazurTransfer.Order13IntegralSections
open MazurTransfer.Order13IntegralPicardLiteralFibreRepresentations
universe u

theorem MazurTransfer.Order13IntegralPicardLiteralFibreRepresentations.literalCurveFibreIso_section (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    (positiveInfinitySection S).val ≫ (literalCurveFibreIso R S).hom =
      (sectionBaseChange S (positiveInfinitySection R)).val  := by sorry
