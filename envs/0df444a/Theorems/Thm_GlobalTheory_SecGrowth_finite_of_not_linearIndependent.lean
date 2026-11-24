-- Prove2me | Theorems.Thm_GlobalTheory_SecGrowth_finite_of_not_linearIndependent
-- name    : GlobalTheory.SecGrowth.finite_of_not_linearIndependent
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:52:48.356265+00:00
-- url     : https://prove2.me/theorems/83930f6f-41b5-473d-a3c4-1c1849a1d037
-- title:
--   Sec Growth: finite of not linear Independent
-- statement:
--   The Sec Growth construction uses the finite of not linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteOfNotLinearIndependent.lean#L211-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteOfNotLinearIndependent.lean#L211-L218

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIndepSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteOfNotLinearIndependent
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
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.SecGrowth

theorem GlobalTheory.SecGrowth.finite_of_not_linearIndependent {R V : Type} [CommRing R] (hR : IsField R) [AddCommGroup V] [Module R V]
    (n : ℕ) (h : ∀ b : Fin n → V, ¬ LinearIndependent R b) : Module.Finite R V := by sorry
