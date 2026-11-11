-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_equicontinuous_CR_derivative_bound_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.equicontinuous_CR_derivative_bound_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:48:22.897854+00:00
-- url     : https://prove2.me/theorems/2906972c-8bfe-4031-9bdc-2af0fcbaa914
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.equicontinuous_CR_derivative_bound_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.equicontinuous_CR_derivative_bound` of [lean/OAI/Geometry/BallPacking/Compactness/FrozenCR.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/FrozenCR.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity`, with `open scoped ContDiff Topology`, `open Set Filter`, `open HolderCompletion`, `open scoped BoundedContinuousFunction`):
--
--   ```lean
--   theorem equicontinuous_CR_derivative_bound_bp240 {ι : Type*} (J : ι → Phase n → End n)
--       (u : ι → ℂ → Phase n) (hu : ∀ i,ContDiff ℝ ∞ (u i))
--       (hJc : ∀ i,Continuous (J i)) (hJ : ∀ i x,Compatible (J i x))
--       (hcr : ∀ i z,PseudoHolomorphicAt (J i) (u i) z)
--       {L G : ℝ} (hL : 0≤L) (hG : 1≤G)
--       (hJL : ∀ i x y,‖J i x-J i y‖≤L*‖x-y‖)
--       (hP : ∀ i x,‖compatibleFrame (J i x)‖≤G)
--       (hPi : ∀ i x,‖(compatibleFrame (J i x)).inverse‖≤G)
--       (hm : ∀ ε : ℝ,0<ε →∃ δ : ℝ,0<δ ∧ ∀ i x y,dist x y<δ →dist (u i x) (u i y)<ε) :
--       ∃ M : ℝ,0<M ∧ ∀ i z,‖fderiv ℝ (u i) z‖≤M
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.Compatible`, `OAI.HigherDimensionalBallPacking.Rigidity.End` and `OAI.HigherDimensionalBallPacking.Rigidity.PseudoHolomorphicAt` (definitions bundle `OAIQ240Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame` (definitions bundle `OAIQ240Bp006` of this split); `OAI.HigherDimensionalBallPacking.Phase` (the published bundle `Def_BallPacking`).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_gradient_bound_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/FrozenCR.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.equicontinuous_CR_derivative_bound)

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp006

section

attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Filter
open HolderCompletion
open scoped BoundedContinuousFunction

variable {n : ℕ}

local instance ecgInst1_rfb62b7_1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance ecgInst2_rfb62b7_1 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
theorem equicontinuous_CR_derivative_bound_bp240 {ι : Type*} (J : ι → Phase n → End n)
    (u : ι → ℂ → Phase n) (hu : ∀ i,ContDiff ℝ ∞ (u i))
    (hJc : ∀ i,Continuous (J i)) (hJ : ∀ i x,Compatible (J i x))
    (hcr : ∀ i z,PseudoHolomorphicAt (J i) (u i) z)
    {L G : ℝ} (hL : 0≤L) (hG : 1≤G)
    (hJL : ∀ i x y,‖J i x-J i y‖≤L*‖x-y‖)
    (hP : ∀ i x,‖compatibleFrame (J i x)‖≤G)
    (hPi : ∀ i x,‖(compatibleFrame (J i x)).inverse‖≤G)
    (hm : ∀ ε : ℝ,0<ε →∃ δ : ℝ,0<δ ∧ ∀ i x y,dist x y<δ →dist (u i x) (u i y)<ε) :
    ∃ M : ℝ,0<M ∧ ∀ i z,‖fderiv ℝ (u i) z‖≤M := by
  sorry

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end
