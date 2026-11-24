-- Prove2me | Theorems.Thm_GlobalTheory_specMap_functionFieldMap
-- name    : GlobalTheory.specMap_functionFieldMap
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:21:53.845515+00:00
-- url     : https://prove2.me/theorems/339de847-c0c1-4e3a-b2a3-f42020f53d9d
-- title:
--   Global Theory: spec Map function Field Map
-- statement:
--   The Global Theory construction uses the spec Map function Field Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringDominatingSubring.lean#L358-L364
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringDominatingSubring.lean#L358-L364

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringDominatingSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
noncomputable section
open GlobalTheory
variable {X X' S : Scheme.{u}} [IsIntegral X] [IsIntegral X']
variable {W : ValuationSubring X.functionField} {x : X}

theorem GlobalTheory.specMap_functionFieldMap (f : X ⟶ X') [IsDominant f] :
    Spec.map (CommRingCat.ofHom (functionFieldMap f)) ≫ genericFieldPoint X' =
      genericFieldPoint X ≫ f := by sorry
