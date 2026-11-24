-- Prove2me | Theorems.Thm_GlobalTheory_SecGrowth_finite_compHom
-- name    : GlobalTheory.SecGrowth.finite_compHom
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:52:37.485081+00:00
-- url     : https://prove2.me/theorems/c1c8393a-a7f1-48da-898b-72262bad043c
-- title:
--   Sec Growth: finite comp Hom
-- statement:
--   The Sec Growth construction uses the finite comp Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteOfNotLinearIndependent.lean#L226-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteOfNotLinearIndependent.lean#L226-L236

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

theorem GlobalTheory.SecGrowth.finite_compHom {K R V : Type} [CommRing K] [CommRing R] (e : K ≃+* R) [AddCommGroup V] [Module R V]
    [Module.Finite R V] :
    letI := Module.compHom V e.toRingHom
    Module.Finite K V := by sorry
