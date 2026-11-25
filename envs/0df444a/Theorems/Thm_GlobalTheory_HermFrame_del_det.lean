-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_del_det
-- name    : GlobalTheory.HermFrame.del_det
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:45:21.092015+00:00
-- url     : https://prove2.me/theorems/50addd55-23f2-419b-a8dd-d7edc0692150
-- title:
--   Herm Frame: del det
-- statement:
--   The Herm Frame construction uses the del det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChernOneEqNegDdcLogDet.lean#L46-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChernOneEqNegDdcLogDet.lean#L46-L56

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

theorem GlobalTheory.HermFrame.del_det (h : MContDiffAt 1 H z) (ξ : E) :
    del (fun x => (H x).det) z ξ = ((H z).adjugate * mdel H z ξ).trace := by sorry
