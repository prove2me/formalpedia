-- Prove2me | Theorems.Thm_HSDoublingWork_entry
-- name    : HSDoublingWork.entry
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:51:52.977792+00:00
-- url     : https://prove2.me/theorems/9d180dfa-eef0-4c9d-86a8-774dacf22ffa
-- title:
--   HSDoubling Work: entry
-- statement:
--   The HSDoubling Work construction uses the entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DoubleSumSwap/SumSwap.lean#L15-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DoubleSumSwap/SumSwap.lean#L15-L24

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_CBCardNC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DoubleSumSwap_SumSwap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open HSDoublingWork
open Formalism.MainNotions.Ext.CutB
variable {N : ℕ} (ε : Fin N → Bool) (z : cBNC ε → ℂ)

theorem HSDoublingWork.entry (x : Fin N × Fin N) : ‖cBpp ε z x.1 x.2‖ ^ 2 = U ε z x + U ε z x.swap := by sorry
