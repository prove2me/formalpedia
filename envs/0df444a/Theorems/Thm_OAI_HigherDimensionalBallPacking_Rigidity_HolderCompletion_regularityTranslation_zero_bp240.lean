-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_regularityTranslation_zero_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_zero_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:10:42.081528+00:00
-- url     : https://prove2.me/theorems/213de206-6dfd-45b6-be54-258016337aaa
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_zero_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_zero` of [lean/OAI/Geometry/BallPacking/Fredholm/TranslationContinuity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/TranslationContinuity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion`, with `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Function Filter`):
--
--   ```lean
--   @[simp] lemma regularityTranslation_zero_bp240 : regularityTranslation b p q w hRS hsupp 0=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Ambient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.COne`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Holder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.JetAmbient` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Pairs` (definitions bundle `OAIQ240Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeModel` (definitions bundle `OAIQ240Bp008` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation` (definitions bundle `OAIQ240Bp022` of this split); `OAI.HigherDimensionalBallPacking.Phase` (the published bundle `Def_BallPacking`).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_smooth_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/TranslationContinuity.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_zero)

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp022

section

attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst6
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B<‖x‖ → J x=standardJ n) (b : ContDiffBump (0:ℂ)) (p q : Phase n)
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst11
variable (w : freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) {R : ℝ}
  (hRS : R+1≤b.rOut) (hsupp : w.val ∈ freeModel (E := Phase n) (Metric.closedBall (0:ℂ) R))
  (hesc : FreeEscapeNeighborhood b p (markedSlope p q w.val) w.val B)
  (hcr : ∀ z, fderiv ℝ (markedCurve p q w.val) z Complex.I =
    J (markedCurve p q w.val z) (fderiv ℝ (markedCurve p q w.val) z 1))

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst8
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst9
@[simp] lemma regularityTranslation_zero_bp240 : regularityTranslation b p q w hRS hsupp 0=0 := by
  sorry

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end
