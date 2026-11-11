-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_actualMarkedChart_derivative_eq_linearized_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_derivative_eq_linearized_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:58:30.120202+00:00
-- url     : https://prove2.me/theorems/ba0242fc-7500-4ba1-a635-0a57074de27f
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_derivative_eq_linearized_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_derivative_eq_linearized` of [lean/OAI/Geometry/BallPacking/Fredholm/TranslationContinuity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/TranslationContinuity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion`, with `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Function Filter`):
--
--   ```lean
--   lemma actualMarkedChart_derivative_eq_linearized_bp240
--       (b₁ : ContDiffBump (0:ℂ)) (hb₁ : Metric.closedBall (0:ℂ) b.rOut ⊆ Metric.closedBall (0:ℂ) b₁.rIn) :
--       fderiv ℝ (actualMarkedChart hJ hstd b p q u) 0 =
--         completedLinearized hJ hstd p q u.val (marked_escape_base b p q u he) b₁ hb₁
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.End`, `OAI.HigherDimensionalBallPacking.Rigidity.standardJ`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Ambient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.COne`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.HMap`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Holder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.JetAmbient` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Pairs` (definitions bundle `OAIQ240Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedHolder` (definitions bundle `OAIQ240Bp005` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedCurve` (definitions bundle `OAIQ240Bp011` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.truncatedCurve` (definitions bundle `OAIQ240Bp014` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst10`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst11`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst14`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst15`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst2` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst9` (definitions bundle `OAIQ240Bp017` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedLinearized` (definitions bundle `OAIQ240Bp018` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart` (definitions bundle `OAIQ240Bp020` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.marked_escape_base` (definitions bundle `OAIQ240Bp021` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedModel` (definitions bundle `OAIQ240Bp024` of this split); `OAI.HigherDimensionalBallPacking.Phase` (the published bundle `Def_BallPacking`).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.Rigidity.fullLineProperPath_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/TranslationContinuity.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_derivative_eq_linearized)

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp020
import Definitions.Def_OAIQ240Bp021

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
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst6
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x=standardJ n) (b : ContDiffBump (0:ℂ)) (p q : Phase n)
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst8
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst11
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst12
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst13
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst14
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst15
variable (u : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))
  (he : ∀ᶠ h in 𝓝 (0 : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)),
    ∀ z : ℂ, b.rIn ≤ ‖z‖ → B < ‖markedCurve p q (u.val+h.val) z‖ ∧
      B < ‖truncatedCurve b p q u.val h.val z‖)

lemma actualMarkedChart_derivative_eq_linearized_bp240
    (b₁ : ContDiffBump (0:ℂ)) (hb₁ : Metric.closedBall (0:ℂ) b.rOut ⊆ Metric.closedBall (0:ℂ) b₁.rIn) :
    fderiv ℝ (actualMarkedChart hJ hstd b p q u) 0 =
      completedLinearized hJ hstd p q u.val (marked_escape_base b p q u he) b₁ hb₁ := by
  sorry

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end
