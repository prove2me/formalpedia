-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_completedZeroOrder_compact_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedZeroOrder_compact_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:46:50.5162+00:00
-- url     : https://prove2.me/theorems/8dfb68b1-3a2a-41ca-870a-0bd0a0d845bc
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedZeroOrder_compact_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedZeroOrder_compact` of [lean/OAI/Geometry/BallPacking/Fredholm/PointwiseMarkedCR.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/PointwiseMarkedCR.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion`, with `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Filter`):
--
--   ```lean
--   lemma completedZeroOrder_compact_bp240 : IsCompactOperator (completedZeroOrder hJ hstd p q u he)
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.End`, `OAI.HigherDimensionalBallPacking.Rigidity.standardJ`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Ambient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.COne`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.HMap`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Holder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.JetAmbient` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Pairs` (definitions bundle `OAIQ240Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedHolder` (definitions bundle `OAIQ240Bp005` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedCurve` (definitions bundle `OAIQ240Bp011` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst1` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst2` (definitions bundle `OAIQ240Bp014` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedZeroOrder` (definitions bundle `OAIQ240Bp018` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedModel` (definitions bundle `OAIQ240Bp024` of this split); `OAI.HigherDimensionalBallPacking.Phase` (the published bundle `Def_BallPacking`).
--
--   **Used by.** The proofs of `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFreeLinearized_fredholm_bp240` and `OAI.HigherDimensionalBallPacking.Rigidity.fullLineProperPath_bp240` of this split import it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/PointwiseMarkedCR.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedZeroOrder_compact)

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp018

section

attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {n : ℕ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst5
local instance compLinInst6_r5738d0_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst7
local instance compLinInst8_r5738d0_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
local instance compLinInst9_r5738d0_1 : NormedAddCommGroup (HMap ℂ (End n)) := inferInstance
local instance compLinInst10_r5738d0_1 : NormedSpace ℝ (HMap ℂ (End n)) := inferInstance
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x=standardJ n) (p q : Phase n) (u : COne ℂ (Phase n))

variable {K : Set ℂ} (hK : IsCompact K) (he : ∀ z ∉ K, B < ‖markedCurve p q u z‖)

variable (b : ContDiffBump (0:ℂ)) (hb : K ⊆ Metric.closedBall (0:ℂ) b.rIn)

local instance compLinInst11_r5738d0_1 : NormedAddCommGroup (markedModel (E := Phase n) K) := inferInstance
local instance compLinInst12_r5738d0_1 : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
local instance compLinInst13_r5738d0_1 : NormedAddCommGroup (supportedHolder (E := Phase n) K) := inferInstance
local instance compLinInst14_r5738d0_1 : NormedSpace ℝ (supportedHolder (E := Phase n) K) := inferInstance
include hK in
lemma completedZeroOrder_compact_bp240 : IsCompactOperator (completedZeroOrder hJ hstd p q u he) := by
  sorry

end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end
