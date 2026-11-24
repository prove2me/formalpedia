-- Prove2me | Theorems.Thm_GlobalTheory_DivisibleHom_isMonHom_of_factor
-- name    : GlobalTheory.DivisibleHom.isMonHom_of_factor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:56.029509+00:00
-- url     : https://prove2.me/theorems/fbc42f49-f0a6-4b43-bbcd-84e236552b16
-- title:
--   Divisible Hom: is Mon Hom of factor
-- statement:
--   The Divisible Hom construction uses the is Mon Hom of factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsEqPowOfTorsionCompEqOne.lean#L113-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsEqPowOfTorsionCompEqOne.lean#L113-L143

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

theorem GlobalTheory.DivisibleHom.isMonHom_of_factor {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B]
    (M : ℕ) [Flat (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left] [Surjective (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left]
    (φ : A ⟶ B) [IsMonHom (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M ≫ φ)] : IsMonHom φ := by sorry
