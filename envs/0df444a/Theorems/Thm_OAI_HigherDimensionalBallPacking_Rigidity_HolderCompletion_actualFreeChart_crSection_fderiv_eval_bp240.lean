-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_actualFreeChart_crSection_fderiv_eval_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualFreeChart_crSection_fderiv_eval_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:58:56.589738+00:00
-- url     : https://prove2.me/theorems/38740a83-18a6-4962-9eaa-22f583f43d4f
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualFreeChart_crSection_fderiv_eval_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualFreeChart_crSection_fderiv_eval` of [lean/OAI/Geometry/BallPacking/Fredholm/FreeLinearization.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FreeLinearization.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion`, with `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Function Filter`):
--
--   ```lean
--   lemma actualFreeChart_crSection_fderiv_eval_bp240 (z : ℂ) :
--       (supportedEval (E := Phase n) (K := Metric.closedBall (0:ℂ) b.rOut) z).comp
--         (fderiv ℝ (actualFreeChart hJ hstd p q b w) 0) =
--       (((BoundedContinuousFunction.evalCLM ℝ z).comp (valueCLM _)).comp
--         ((crSectionDeriv (actualStructureBound hJ hstd) p (complexSlope (markedSlope p q w.val)) w.val).comp
--           (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)).subtypeL))
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.End`, `OAI.HigherDimensionalBallPacking.Rigidity.standardJ`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Ambient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.COne`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.HMap`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Holder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.JetAmbient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Pairs` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.valueCLM` (definitions bundle `OAIQ240Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.complexSlope` (definitions bundle `OAIQ240Bp001` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedHolder` (definitions bundle `OAIQ240Bp005` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeModel` (definitions bundle `OAIQ240Bp008` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedSlope` (definitions bundle `OAIQ240Bp011` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedEval` (definitions bundle `OAIQ240Bp014` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualStructureBound`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst2` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst23` (definitions bundle `OAIQ240Bp017` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualFreeChart`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst17`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst21` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst22` (definitions bundle `OAIQ240Bp020` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCurve` (definitions bundle `OAIQ240Bp024` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectionDeriv` (definitions bundle `OAIQ240Bp025` of this split); `OAI.HigherDimensionalBallPacking.Phase` (the published bundle `Def_BallPacking`).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualFreeChart_fderiv_fredholm_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FreeLinearization.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualFreeChart_crSection_fderiv_eval)

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp020

section

attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HolderCompletion
variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst6
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x=standardJ n) (p q : Phase n) (u : COne ℂ (Phase n))
  {K : Set ℂ} (hK : IsCompact K) (he : ∀ z ∉ K, B < ‖markedCurve p q u z‖)

variable (b : ContDiffBump (0:ℂ))
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst8
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst11
local instance afInst12_rda12d8_1 : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst13
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst15
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst16
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst17
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst18
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst19
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst20
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst21
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst22
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst23
variable (w : freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))
  (hesc : ∀ᶠ v in 𝓝 (0 : freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)),
    ∀ z, b.rIn ≤ ‖z‖ → B < ‖affineCurve p (complexSlope (markedSlope p q w.val)) (w.val+v.val) z‖)

include hesc in
lemma actualFreeChart_crSection_fderiv_eval_bp240 (z : ℂ) :
    (supportedEval (E := Phase n) (K := Metric.closedBall (0:ℂ) b.rOut) z).comp
      (fderiv ℝ (actualFreeChart hJ hstd p q b w) 0) =
    (((BoundedContinuousFunction.evalCLM ℝ z).comp (valueCLM _)).comp
      ((crSectionDeriv (actualStructureBound hJ hstd) p (complexSlope (markedSlope p q w.val)) w.val).comp
        (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)).subtypeL)) := by
  sorry

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end
