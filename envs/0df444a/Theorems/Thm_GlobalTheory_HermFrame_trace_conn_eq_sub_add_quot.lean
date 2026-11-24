-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_trace_conn_eq_sub_add_quot
-- name    : GlobalTheory.HermFrame.trace_conn_eq_sub_add_quot
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:45:02.787559+00:00
-- url     : https://prove2.me/theorems/b590f2d6-c8a1-4b0a-8e34-a92d9a4d8964
-- title:
--   Herm Frame: trace conn eq sub add quot
-- statement:
--   The Herm Frame construction uses the trace conn eq sub add quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChernOneEqNegDdcLogDet.lean#L108-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChernOneEqNegDdcLogDet.lean#L108-L120

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
variable [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
  {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}

theorem GlobalTheory.HermFrame.trace_conn_eq_sub_add_quot (h : MContDiffAt 1 H z) (hu : IsUnit (H z).det)
    (hs : IsUnit (subGram (H z)).det) (ξ : E) : (conn H z ξ).trace =
      (conn (fun x => subGram (H x)) z ξ).trace + (conn (fun x => quotGram (H x)) z ξ).trace := by sorry
