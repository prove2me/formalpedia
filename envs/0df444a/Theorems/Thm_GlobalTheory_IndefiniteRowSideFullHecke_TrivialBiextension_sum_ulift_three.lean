-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_TrivialBiextension_sum_ulift_three
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension.sum_ulift_three
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:16:03.675328+00:00
-- url     : https://prove2.me/theorems/f3d371e4-6609-4591-8b7f-bfcb9186bdc4
-- title:
--   Trivial Biextension: sum ulift three
-- statement:
--   The Trivial Biextension construction uses the sum ulift three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/TrivialBiextension.lean#L133-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/TrivialBiextension.lean#L133-L134

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_TrivialBiextension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
universe u
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

theorem GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension.sum_ulift_three (f : ULift.{u} (Fin 3) → ℤ) : ∑ k, f k = f ⟨0⟩ + f ⟨1⟩ + f ⟨2⟩ := by sorry
