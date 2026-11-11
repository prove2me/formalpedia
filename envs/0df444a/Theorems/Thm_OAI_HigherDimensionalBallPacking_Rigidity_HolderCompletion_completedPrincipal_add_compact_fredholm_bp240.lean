-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_completedPrincipal_add_compact_fredholm_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_add_compact_fredholm_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:09:12.747632+00:00
-- url     : https://prove2.me/theorems/fc278da0-60e7-4c00-b47b-221f05b4cec7
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_add_compact_fredholm_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_add_compact_fredholm` of [lean/OAI/Geometry/BallPacking/Fredholm/FrameFredholm.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FrameFredholm.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion`, with `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Filter`):
--
--   ```lean
--   lemma completedPrincipal_add_compact_fredholm_bp240
--       (C : markedModel (E := Phase n) K →L[ℝ] supportedHolder (E := Phase n) K)
--       (hC : IsCompactOperator C) :
--       (completedPrincipal hJ hstd p q u he+C).IsFredholm ∧
--         Module.finrank ℝ (completedPrincipal hJ hstd p q u he+C).ker =
--           Module.finrank ℝ (supportedHolder (E := Phase n) K ⧸ (completedPrincipal hJ hstd p q u he+C).range)
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.Compatible`, `OAI.HigherDimensionalBallPacking.Rigidity.End`, `OAI.HigherDimensionalBallPacking.Rigidity.standardJ`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Ambient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.COne`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.HMap`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Holder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.JetAmbient` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Pairs` (definitions bundle `OAIQ240Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedHolder` (definitions bundle `OAIQ240Bp005` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccFrameInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccFrameInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedCurve` (definitions bundle `OAIQ240Bp011` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccFrameInst3` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccFrameInst5` (definitions bundle `OAIQ240Bp015` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedModel` (definitions bundle `OAIQ240Bp024` of this split); `OAI.HigherDimensionalBallPacking.Phase` (the published bundle `Def_BallPacking`).
--
--   **Used by.** The proofs of `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFreeLinearized_fredholm_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFreePrincipal_fredholm_bp240` and `OAI.HigherDimensionalBallPacking.Rigidity.fullLineProperPath_bp240` of this split import it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FrameFredholm.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_add_compact_fredholm)

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp015

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

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccFrameInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccFrameInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccFrameInst3
local instance ccFrameInst4_r8e4656_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccFrameInst5
local instance ccFrameInst6_r8e4656_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
local instance ccFrameInst7_r8e4656_1 : NormedAddCommGroup (COne ℂ (End n)) := inferInstance
local instance ccFrameInst8_r8e4656_1 : NormedSpace ℝ (COne ℂ (End n)) := inferInstance
local instance ccFrameInst9_r8e4656_1 : NormedAddCommGroup (HMap ℂ (End n)) := inferInstance
local instance ccFrameInst10_r8e4656_1 : NormedSpace ℝ (HMap ℂ (End n)) := inferInstance
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x=standardJ n) (p q : Phase n) (u : COne ℂ (Phase n))

variable {K : Set ℂ} (hK : IsCompact K) (he : ∀ z ∉ K, B < ‖markedCurve p q u z‖)

local instance ccFrameInst11_r8e4656_1 : NormedAddCommGroup (markedModel (E := Phase n) K) := inferInstance
local instance ccFrameInst12_r8e4656_1 : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
local instance ccFrameInst13_r8e4656_1 : NormedAddCommGroup (supportedHolder (E := Phase n) K) := inferInstance
local instance ccFrameInst14_r8e4656_1 : NormedSpace ℝ (supportedHolder (E := Phase n) K) := inferInstance
include hc hK in
lemma completedPrincipal_add_compact_fredholm_bp240
    (C : markedModel (E := Phase n) K →L[ℝ] supportedHolder (E := Phase n) K)
    (hC : IsCompactOperator C) :
    (completedPrincipal hJ hstd p q u he+C).IsFredholm ∧
      Module.finrank ℝ (completedPrincipal hJ hstd p q u he+C).ker =
        Module.finrank ℝ (supportedHolder (E := Phase n) K ⧸ (completedPrincipal hJ hstd p q u he+C).range) := by
  sorry

end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end
