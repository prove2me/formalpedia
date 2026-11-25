-- Prove2me | Theorems.Thm_GlobalTheory_MinorGerm_main
-- name    : GlobalTheory.MinorGerm.main
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:44:43.02779+00:00
-- url     : https://prove2.me/theorems/5923a128-8369-4b33-b777-7ed8836d98b9
-- title:
--   Minor Germ: main
-- statement:
--   The Minor Germ construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L559-L560
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L559-L560

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
noncomputable section
open GlobalTheory GlobalTheory.MinorGerm

theorem GlobalTheory.MinorGerm.main : MON ∧ MONTypes := by sorry
