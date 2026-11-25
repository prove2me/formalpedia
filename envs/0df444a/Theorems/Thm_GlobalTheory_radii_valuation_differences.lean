-- Prove2me | Theorems.Thm_GlobalTheory_radii_valuation_differences
-- name    : GlobalTheory.radii_valuation_differences
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:54:50.529607+00:00
-- url     : https://prove2.me/theorems/c353e449-9e34-4c4b-aeed-2c4edc5272c3
-- title:
--   Global Theory: radii valuation differences
-- statement:
--   The Global Theory construction uses the radii valuation differences property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RadiiValuationDifferences.lean#L142-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RadiiValuationDifferences.lean#L142-L145

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RadiiValuationDifferences
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
open GlobalTheory
open RadiiIdentities

theorem GlobalTheory.radii_valuation_differences :
    Formalism.L2.FormalSeriesBounds.EInt ∧ I1 ∧ I2 ∧ ValOther ∧ WeightConditionIff ∧ F5 := by sorry
