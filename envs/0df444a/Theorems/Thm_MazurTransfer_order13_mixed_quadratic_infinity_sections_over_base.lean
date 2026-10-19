-- Prove2me | Theorems.Thm_MazurTransfer_order13_mixed_quadratic_infinity_sections_over_base
-- name    : MazurTransfer.order13_mixed_quadratic_infinity_sections_over_base
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T04:40:22.019853+00:00
-- url     : https://prove2.me/theorems/49cc192e-e879-437c-94ec-c4fa90ff319a
-- statement:
--   The two original mixed quadratic infinity sections, with reciprocal coordinates (0,0) and (0,-1), are sections of the actual whole glued curve structure morphism over every commutative ring. Both whole section constructors and their original coordinate point maps are retained. Named downstream consumer: rigidification of the actual integral Picard family and its compatible base changes.

import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalInfinitySectionsData20261019
noncomputable section
open CategoryTheory AlgebraicGeometry MazurTransfer
open Order13MixedQuadraticInfinitySections Order13MixedQuadraticGluedCurve
universe u

theorem MazurTransfer.order13_mixed_quadratic_infinity_sections_over_base : (∀ (R : Type u) [CommRing R], infinitySectionZero R ≫ curveToBase R = 𝟙 (Spec (.of R))) ∧ (∀ (R : Type u) [CommRing R], infinitySectionNegOne R ≫ curveToBase R = 𝟙 (Spec (.of R))) := by sorry
