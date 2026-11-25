-- Prove2me | Theorems.Thm_HSDoublingWork_sumSwap
-- name    : HSDoublingWork.sumSwap
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:52:02.392617+00:00
-- url     : https://prove2.me/theorems/ed29a3a5-a993-4e33-808b-74961f74be81
-- title:
--   HSDoubling Work: sum Swap
-- statement:
--   The HSDoubling Work construction uses the sum Swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DoubleSumSwap/SumSwap.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DoubleSumSwap/SumSwap.lean#L33-L34

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

theorem HSDoublingWork.sumSwap : ∑ x : Fin N × Fin N, U ε z x.swap = ∑ x, U ε z x := by sorry
