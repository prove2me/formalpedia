-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_trace_curv_eq_sub_add_quot
-- name    : GlobalTheory.HermFrame.trace_curv_eq_sub_add_quot
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:07:16.261278+00:00
-- url     : https://prove2.me/theorems/254011fd-998b-5cc6-9ec8-ccbdd97ef3c6
-- title:
--   Herm Frame: trace curv eq sub add quot
-- statement:
--   The Herm Frame construction uses the trace curv eq sub add quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChernOneEqNegDdcLogDet.lean#L122-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChernOneEqNegDdcLogDet.lean#L122-L140

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

theorem GlobalTheory.HermFrame.trace_curv_eq_sub_add_quot (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det)
    (hs : IsUnit (subGram (H z)).det) (ξ η : E) : (curv H z ξ η).trace =
      (curv (fun x => subGram (H x)) z ξ η).trace +
        (curv (fun x => quotGram (H x)) z ξ η).trace := by sorry
