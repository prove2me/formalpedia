-- Prove2me | Theorems.Thm_GlobalTheory_ThetaAddition_left_mem
-- name    : GlobalTheory.ThetaAddition.left_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:46:37.494748+00:00
-- url     : https://prove2.me/theorems/ea355f1c-5fa5-4cca-8b3f-287bd72fc05f
-- title:
--   Theta Addition: left mem
-- statement:
--   The Theta Addition construction uses the left mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AdditionLevelTwoMul.lean#L26-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AdditionLevelTwoMul.lean#L26-L37

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

theorem GlobalTheory.ThetaAddition.left_mem {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (N : ℕ) {f f' : (Fin g → ℂ) → ℂ}
    (hf : f ∈ thetaLevel N τ) (hf' : f' ∈ thetaLevel N τ) (w : Fin g → ℂ) :
    (fun z => f (z + w) * f' (z - w)) ∈ thetaLevel (2 * N) τ := by sorry
