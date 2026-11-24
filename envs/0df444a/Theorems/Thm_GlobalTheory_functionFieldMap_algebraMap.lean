-- Prove2me | Theorems.Thm_GlobalTheory_functionFieldMap_algebraMap
-- name    : GlobalTheory.functionFieldMap_algebraMap
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:54:04.875839+00:00
-- url     : https://prove2.me/theorems/1defe039-6d4e-48ee-ab7f-096bc162c199
-- title:
--   Global Theory: function Field Map algebra Map
-- statement:
--   The Global Theory construction uses the function Field Map algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringDominatingSubring.lean#L366-L379
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringDominatingSubring.lean#L366-L379

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

theorem GlobalTheory.functionFieldMap_algebraMap (f : X ⟶ X') [IsDominant f] (x : X)
    (a : X'.presheaf.stalk (f x)) :
    functionFieldMap f (algebraMap _ X'.functionField a) =
      algebraMap _ X.functionField (f.stalkMap x a) := by sorry
