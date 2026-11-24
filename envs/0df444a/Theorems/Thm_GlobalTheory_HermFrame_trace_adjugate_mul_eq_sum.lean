-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_trace_adjugate_mul_eq_sum
-- name    : GlobalTheory.HermFrame.trace_adjugate_mul_eq_sum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:45:08.332625+00:00
-- url     : https://prove2.me/theorems/b511373c-0853-4293-87d7-582814fb3ad3
-- title:
--   Herm Frame: trace adjugate mul eq sum
-- statement:
--   The Herm Frame construction uses the trace adjugate mul eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChernOneEqNegDdcLogDet.lean#L26-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChernOneEqNegDdcLogDet.lean#L26-L44

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

theorem GlobalTheory.HermFrame.trace_adjugate_mul_eq_sum (A B : Matrix n n ℂ) :
    (A.adjugate * B).trace = ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ : ℂ) *
      ∑ i, (∏ j ∈ Finset.univ.erase i, A (σ j) j) * B (σ i) i := by sorry
