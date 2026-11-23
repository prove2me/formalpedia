-- Prove2me | Theorems.Thm_GlobalTheory_FormalLog_pderiv_comm
-- name    : GlobalTheory.FormalLog.pderiv_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:42.958001+00:00
-- url     : https://prove2.me/theorems/826134aa-b646-4f60-a56f-a77549c682d1
-- title:
--   Formal Log: pderiv comm
-- statement:
--   The Formal Log construction uses the pderiv comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EqCOfPderivZero.lean#L19-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EqCOfPderivZero.lean#L19-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EqCOfPderivZero
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {σ τ : Type}

theorem GlobalTheory.FormalLog.pderiv_comm (u v : τ) (g : MvPowerSeries τ k) : pderiv k u (pderiv k v g) = pderiv k v (pderiv k u g) := by sorry
