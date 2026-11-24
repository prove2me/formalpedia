-- Prove2me | Theorems.Thm_GlobalTheory_DivisibleHom_isMonHom_of_mul_points
-- name    : GlobalTheory.DivisibleHom.isMonHom_of_mul_points
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:50:38.700898+00:00
-- url     : https://prove2.me/theorems/e61dae16-a55c-48eb-8a30-45a4c9d032d3
-- title:
--   Divisible Hom: is Mon Hom of mul points
-- statement:
--   The Divisible Hom construction uses the is Mon Hom of mul points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsEqPowOfTorsionCompEqOne.lean#L46-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsEqPowOfTorsionCompEqOne.lean#L46-L61

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsEqPowOfTorsionCompEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.DivisibleHom
variable {S : Scheme.{0}}
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}}

theorem GlobalTheory.DivisibleHom.isMonHom_of_mul_points {G H : Over S} [GrpObj G] [GrpObj H] (e : G ⟶ H)
    (mul : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ e = (x ≫ e) * (y ≫ e)) : IsMonHom e := by sorry
