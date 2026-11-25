-- Prove2me | Theorems.Thm_GlobalTheory_ThetaAddition_right_mem
-- name    : GlobalTheory.ThetaAddition.right_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:44:57.979262+00:00
-- url     : https://prove2.me/theorems/45db80b8-e19a-50f9-ab1b-7e5ebf54878e
-- title:
--   Theta Addition: right mem
-- statement:
--   The Theta Addition construction uses the right mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AdditionLevelTwoMul.lean#L39-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AdditionLevelTwoMul.lean#L39-L52

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SpanEvalEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AdditionLevelTwoMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaAddition

theorem GlobalTheory.ThetaAddition.right_mem {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (N : ℕ) {f f' : (Fin g → ℂ) → ℂ}
    (hf : f ∈ thetaLevel N τ) (hf' : f' ∈ thetaLevel N τ) (z : Fin g → ℂ) :
    (fun w => f (z + w) * f' (z - w)) ∈ thetaLevel (2 * N) τ := by sorry
