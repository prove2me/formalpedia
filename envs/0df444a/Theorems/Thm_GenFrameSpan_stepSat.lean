-- Prove2me | Theorems.Thm_GenFrameSpan_stepSat
-- name    : GenFrameSpan.stepSat
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:50:48.242023+00:00
-- url     : https://prove2.me/theorems/4d35359a-6225-4049-86db-d77e209407ee
-- title:
--   Gen Frame Span: step Sat
-- statement:
--   The Gen Frame Span construction uses the step Sat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/GenFrameSBOfSpan.lean#L8-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/GenFrameSBOfSpan.lean#L8-L8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_GenFrameSBOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_StepBack
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatProj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_GenFrameSBOfSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GenFrameSpan

theorem GenFrameSpan.stepSat : StepSat := by sorry
