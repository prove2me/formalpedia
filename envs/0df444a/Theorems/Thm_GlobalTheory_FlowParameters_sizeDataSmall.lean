-- Prove2me | Theorems.Thm_GlobalTheory_FlowParameters_sizeDataSmall
-- name    : GlobalTheory.FlowParameters.sizeDataSmall
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:33:02.416311+00:00
-- url     : https://prove2.me/theorems/b94f37f4-30b8-4e14-9a9c-a23f357c2984
-- title:
--   Flow Parameters: size Data Small
-- statement:
--   The Flow Parameters construction uses the size Data Small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ParametersSmallBound.lean#L54-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ParametersSmallBound.lean#L54-L104

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ParametersSmallBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open GlobalTheory GlobalTheory.FlowParameters

theorem GlobalTheory.FlowParameters.sizeDataSmall : ParametersSmall := by sorry
