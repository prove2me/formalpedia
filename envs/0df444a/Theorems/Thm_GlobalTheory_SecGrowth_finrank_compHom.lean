-- Prove2me | Theorems.Thm_GlobalTheory_SecGrowth_finrank_compHom
-- name    : GlobalTheory.SecGrowth.finrank_compHom
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:52:14.253349+00:00
-- url     : https://prove2.me/theorems/eab39d70-4b98-4500-9881-58529663cd8b
-- title:
--   Sec Growth: finrank comp Hom
-- statement:
--   The Sec Growth construction uses the finrank comp Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteOfNotLinearIndependent.lean#L220-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteOfNotLinearIndependent.lean#L220-L224

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

theorem GlobalTheory.SecGrowth.finrank_compHom {K R V : Type} [CommRing K] [CommRing R] (e : K ≃+* R) [AddCommGroup V] [Module R V] :
    letI := Module.compHom V e.toRingHom
    Module.finrank K V = Module.finrank R V := by sorry
