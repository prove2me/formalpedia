-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_completed_markedCurve_contDiff_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completed_markedCurve_contDiff_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:49:24.097892+00:00
-- url     : https://prove2.me/theorems/ecd8c867-5914-481e-ac98-16027f56b4dc
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completed_markedCurve_contDiff_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completed_markedCurve_contDiff` of [lean/OAI/Geometry/BallPacking/Fredholm/TranslationContinuity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/TranslationContinuity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion`, with `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Function Filter`):
--
--   ```lean
--   lemma completed_markedCurve_contDiff_bp240 (u : COne ℂ (Phase n)) (ha : markedSlope p q u ≠ 0)
--       (hcr : ∀ z, fderiv ℝ (markedCurve p q u) z Complex.I =
--         J (markedCurve p q u z) (fderiv ℝ (markedCurve p q u) z 1)) :
--       ContDiff ℝ ∞ (markedCurve p q u)
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.Compatible`, `OAI.HigherDimensionalBallPacking.Rigidity.End`, `OAI.HigherDimensionalBallPacking.Rigidity.standardJ`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Ambient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.COne`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Holder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.JetAmbient` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Pairs` (definitions bundle `OAIQ240Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedCurve` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedSlope` (definitions bundle `OAIQ240Bp011` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.azInst1` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.azInst2` (definitions bundle `OAIQ240Bp018` of this split); `OAI.HigherDimensionalBallPacking.Phase` (the published bundle `Def_BallPacking`).
--
--   **Used by.** The proofs of `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.isolatedFullLineZeros_compact_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.completed_line_closed_bp240` and `OAI.HigherDimensionalBallPacking.Rigidity.fullLineEndpointMap_bp240` of this split import it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/TranslationContinuity.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completed_markedCurve_contDiff)

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
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
section
variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.azInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.azInst2
local instance azInst3_r2383dc_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance azInst4_r2383dc_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance azInst5_r2383dc_1 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance azInst6_r2383dc_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B<‖x‖ → J x=standardJ n) (p q : Phase n)

include hJ hc hstd in
lemma completed_markedCurve_contDiff_bp240 (u : COne ℂ (Phase n)) (ha : markedSlope p q u ≠ 0)
    (hcr : ∀ z, fderiv ℝ (markedCurve p q u) z Complex.I =
      J (markedCurve p q u z) (fderiv ℝ (markedCurve p q u) z 1)) :
    ContDiff ℝ ∞ (markedCurve p q u) := by
  sorry

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end
