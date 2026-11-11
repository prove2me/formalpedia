-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_isolatedFullLineZeros_compact_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.isolatedFullLineZeros_compact_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:57:44.460033+00:00
-- url     : https://prove2.me/theorems/17694632-4e23-4764-b0dc-09b16e0015ad
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.isolatedFullLineZeros_compact_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.isolatedFullLineZeros_compact` of [lean/OAI/Geometry/BallPacking/Continuation/ParameterizedImplicit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Continuation/ParameterizedImplicit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion`, with `open scoped ContDiff Topology`, `open Filter`, `open scoped BoundedContinuousFunction`, `open Set Function`):
--
--   ```lean
--   lemma isolatedFullLineZeros_compact_bp240
--       (hc : IsCompact (fullMarkedZeroSet J p q)) :
--       IsCompact (isolatedFullLineZeros b hJs hJ hJc b₁ p q (M := M) (δ := δ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.Compatible`, `OAI.HigherDimensionalBallPacking.Rigidity.End`, `OAI.HigherDimensionalBallPacking.Rigidity.standardJ`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Ambient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.COne`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Holder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.JetAmbient` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Pairs` (definitions bundle `OAIQ240Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.MarkedEscapeNeighborhood` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedBoundedDomain` (definitions bundle `OAIQ240Bp017` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.exactMarkedZeroSet`, `OAI.HigherDimensionalBallPacking.Rigidity.fullMarkedZeroSet` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.isolatedFullLineZeros` (definitions bundle `OAIQ240Bp021` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedModel` (definitions bundle `OAIQ240Bp024` of this split); `OAI.HigherDimensionalBallPacking.Phase` (the published bundle `Def_BallPacking`).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.Rigidity.fullLineProperPath_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Continuation/ParameterizedImplicit.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.isolatedFullLineZeros_compact)

import Mathlib
import Definitions.Def_BallPacking
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
open scoped ContDiff Topology
open Filter
open scoped BoundedContinuousFunction
open Set Function

variable {n : ℕ}
variable (b : ContDiffBump (0:ℂ))

variable {J : Phase n → End n} (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
  (hJc : HasCompactSupport (fun x => J x-standardJ n))
  (b₁ : ContDiffBump (0:ℂ)) (p q : Phase n)
  (hb₁ : Metric.closedBall (0:ℂ) b.rOut⊆Metric.closedBall (0:ℂ) b₁.rIn)
  {B M δ : ℝ} (hstd : ∀ x,B<‖x‖ →J x=standardJ n) (hδ : 0<δ)
  (he : ∀ w∈markedBoundedDomain p q M δ,MarkedEscapeNeighborhood b p q w B)
  (hbound : ∀ v∈exactMarkedZeroSet J p q,v.2∈markedBoundedDomain p q M δ)

local instance gid1_r38c9f3_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance gid2_r38c9f3_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance gid3_r38c9f3_1 : NormedAddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gid4_r38c9f3_1 : NormedSpace ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gid5_r38c9f3_1 : NormedAddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gid6_r38c9f3_1 : NormedSpace ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
include hb₁ hstd hδ he hbound in
lemma isolatedFullLineZeros_compact_bp240
    (hc : IsCompact (fullMarkedZeroSet J p q)) :
    IsCompact (isolatedFullLineZeros b hJs hJ hJc b₁ p q (M := M) (δ := δ)) := by
  sorry

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

end

end OAI
end
