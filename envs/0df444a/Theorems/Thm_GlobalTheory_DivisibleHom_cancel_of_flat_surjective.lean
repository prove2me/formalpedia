-- Prove2me | Theorems.Thm_GlobalTheory_DivisibleHom_cancel_of_flat_surjective
-- name    : GlobalTheory.DivisibleHom.cancel_of_flat_surjective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:31.836069+00:00
-- url     : https://prove2.me/theorems/5c55a821-a155-4913-be91-d8fe0e2af0e7
-- title:
--   Divisible Hom: cancel of flat surjective
-- statement:
--   The Divisible Hom construction uses the cancel of flat surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsEqPowOfTorsionCompEqOne.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsEqPowOfTorsionCompEqOne.lean#L16-L21

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

theorem GlobalTheory.DivisibleHom.cancel_of_flat_surjective {X Y Z : Over S} (e : X ⟶ Y) [Flat e.left]
    [Surjective e.left] {f g : Y ⟶ Z} (h : e ≫ f = e ≫ g) : f = g := by sorry
