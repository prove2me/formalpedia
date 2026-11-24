-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_del_finsetProd
-- name    : GlobalTheory.HermFrame.del_finsetProd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:44:55.578947+00:00
-- url     : https://prove2.me/theorems/8da381a9-dd95-4b0c-a228-dff4364ed16c
-- title:
--   Herm Frame: del finset Prod
-- statement:
--   The Herm Frame construction uses the del finset Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChernOneEqNegDdcLogDet.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChernOneEqNegDdcLogDet.lean#L14-L20

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

theorem GlobalTheory.HermFrame.del_finsetProd {ι : Type*} [DecidableEq ι] (t : Finset ι) {f : ι → E → ℂ} {z : E}
    (h : ∀ i ∈ t, DifferentiableAt ℝ (f i) z) (ξ : E) :
    del (fun x => ∏ i ∈ t, f i x) z ξ = ∑ i ∈ t, (∏ j ∈ t.erase i, f j z) * del (f i) z ξ := by sorry
