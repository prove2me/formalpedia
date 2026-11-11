-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_affineCurve_translation_CR_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCurve_translation_CR_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:52:18.525891+00:00
-- url     : https://prove2.me/theorems/bbe5ffd3-92aa-485f-afe1-f436fedd14c0
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCurve_translation_CR_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCurve_translation_CR` of [lean/OAI/Geometry/BallPacking/Fredholm/TranslationContinuity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/TranslationContinuity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion`, with `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Function Filter`):
--
--   ```lean
--   lemma affineCurve_translation_CR_bp240 (J : E → E →L[ℝ] E) (p a : E) (u : COne ℂ E)
--       (hcr : ∀ z, fderiv ℝ (affineCurve p (complexSlope a) u) z Complex.I =
--         J (affineCurve p (complexSlope a) u z) (fderiv ℝ (affineCurve p (complexSlope a) u) z 1)) (t z : ℂ) :
--       fderiv ℝ (affineCurve p (complexSlope a) (u+translationVariation a u t)) z Complex.I =
--         J (affineCurve p (complexSlope a) (u+translationVariation a u t) z)
--           (fderiv ℝ (affineCurve p (complexSlope a) (u+translationVariation a u t)) z 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Ambient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.COne`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Holder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.JetAmbient` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Pairs` (definitions bundle `OAIQ240Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.complexSlope` (definitions bundle `OAIQ240Bp001` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.translationVariation` (definitions bundle `OAIQ240Bp017` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCurve` (definitions bundle `OAIQ240Bp024` of this split).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_smooth_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/TranslationContinuity.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCurve_translation_CR)

import Mathlib
import Definitions.Def_OAIQ240Bp017

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

local instance teInst1_r4bb105_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance teInst2_r4bb105_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance teInst3_r4bb105_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance teInst4_r4bb105_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
lemma affineCurve_translation_CR_bp240 (J : E → E →L[ℝ] E) (p a : E) (u : COne ℂ E)
    (hcr : ∀ z, fderiv ℝ (affineCurve p (complexSlope a) u) z Complex.I =
      J (affineCurve p (complexSlope a) u z) (fderiv ℝ (affineCurve p (complexSlope a) u) z 1)) (t z : ℂ) :
    fderiv ℝ (affineCurve p (complexSlope a) (u+translationVariation a u t)) z Complex.I =
      J (affineCurve p (complexSlope a) (u+translationVariation a u t) z)
        (fderiv ℝ (affineCurve p (complexSlope a) (u+translationVariation a u t)) z 1) := by
  sorry

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

end

end OAI
end
