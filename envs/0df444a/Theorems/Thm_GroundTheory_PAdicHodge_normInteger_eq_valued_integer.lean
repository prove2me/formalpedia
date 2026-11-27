-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_normInteger_eq_valued_integer
-- name    : GroundTheory.PAdicHodge.normInteger_eq_valued_integer
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:01:13.204901+00:00
-- url     : https://prove2.me/theorems/af77aaad-fbb5-52c3-97ff-e548d3d5e5c7
-- title:
--   PAdic Hodge: norm Integer eq valued integer
-- statement:
--   The PAdic Hodge construction uses the norm Integer eq valued integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidField.lean#L27-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidField.lean#L27-L27

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open NNReal
variable (K : Type*) [NormedField K] [IsUltrametricDist K]
variable {K}
open scoped NormedField

theorem GroundTheory.PAdicHodge.normInteger_eq_valued_integer : normInteger K = Valued.integer K := by sorry
