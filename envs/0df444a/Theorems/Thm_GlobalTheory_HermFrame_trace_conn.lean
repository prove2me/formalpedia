-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_trace_conn
-- name    : GlobalTheory.HermFrame.trace_conn
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:45:06.889426+00:00
-- url     : https://prove2.me/theorems/6e113773-2070-4daf-b586-03b66a4922d6
-- title:
--   Herm Frame: trace conn
-- statement:
--   The Herm Frame construction uses the trace conn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChernOneEqNegDdcLogDet.lean#L58-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChernOneEqNegDdcLogDet.lean#L58-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChernOneEqNegDdcLogDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}
variable [Fintype n] [DecidableEq n] {H : E → Matrix n n ℂ} {z : E}

theorem GlobalTheory.HermFrame.trace_conn (h : MContDiffAt 1 H z) (hu : IsUnit (H z).det) (ξ : E) :
    (conn H z ξ).trace = (H z).det⁻¹ * del (fun x => (H x).det) z ξ := by sorry
