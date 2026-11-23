-- Prove2me | Theorems.Thm_GlobalTheory_SliceOpDeriv_continuous_elim_pair
-- name    : GlobalTheory.SliceOpDeriv.continuous_elim_pair
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:05.855937+00:00
-- url     : https://prove2.me/theorems/48f01c00-a2f4-44b1-83c4-370738931b53
-- title:
--   Slice Op Deriv: continuous elim pair
-- statement:
--   The Slice Op Deriv construction uses the continuous elim pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PartialOperatorFderivFormula.lean#L94-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PartialOperatorFderivFormula.lean#L94-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SeminormSliceRLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivPdLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialOperatorFderivFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.SliceOpDeriv
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']

theorem GlobalTheory.SliceOpDeriv.continuous_elim_pair :
    Continuous (fun p : (κ → V) × (κ₁' → V) => (Sum.elim p.1 p.2 : κ ⊕ κ₁' → V)) := by sorry
