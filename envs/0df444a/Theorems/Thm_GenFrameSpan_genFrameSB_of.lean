-- Prove2me | Theorems.Thm_GenFrameSpan_genFrameSB_of
-- name    : GenFrameSpan.genFrameSB_of
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:50:31.27692+00:00
-- url     : https://prove2.me/theorems/2b517d00-30ea-442f-aafd-9a31565970a2
-- title:
--   Gen Frame Span: gen Frame SB of
-- statement:
--   The Gen Frame Span construction uses the gen Frame SB of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/GenFrameSBOf.lean#L7-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/GenFrameSBOf.lean#L7-L9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_NablaSpanC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_GenFrameSBOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GenFrameSpan
open CutKW

theorem GenFrameSpan.genFrameSB_of (hb : StepBack) (hs : StepSpan) (ht : StepSat) : CutKW.KWsb := by sorry
