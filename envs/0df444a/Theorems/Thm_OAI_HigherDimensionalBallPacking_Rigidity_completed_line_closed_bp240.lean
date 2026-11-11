-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_completed_line_closed_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.completed_line_closed_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:00:17.454618+00:00
-- url     : https://prove2.me/theorems/a00fc1d4-69e4-4f6e-b8f2-3f806815673f
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.completed_line_closed_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.completed_line_closed` of [lean/OAI/Geometry/BallPacking/Compactness/ResidualCauchy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/ResidualCauchy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity`, with `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Filter`, `open HolderCompletion`):
--
--   ```lean
--   lemma completed_line_closed_bp240 {J : Phase n → End n}
--       (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
--       (hJc : HasCompactSupport (fun x => J x-standardJ n))
--       {S T : ℝ} (hST : S<T) (hT : T<1) (hout : ∀ x,S < capacity x →J x=standardJ n)
--       {p q : Phase n} (hpq : p≠q) {t : ℕ → ℝ} (ht : ∀ i,t i∈Icc (0:ℝ) 1)
--       {s : ℝ} (hs : Tendsto t atTop (𝓝 s))
--       {w : ℕ → COne ℂ (Phase n)} {v : COne ℂ (Phase n)} (hw : Tendsto w atTop (𝓝 v))
--       (hw0 : ∀ i,cValue (w i) 0=0)
--       (hu : ∀ i,AffineLineCurve (lineHomotopy J (t i)) p q (markedCurve p q (w i))) :
--       AffineLineCurve (lineHomotopy J s) p q (markedCurve p q v)
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.AffineLineCurve`, `OAI.HigherDimensionalBallPacking.Rigidity.Compatible`, `OAI.HigherDimensionalBallPacking.Rigidity.End`, `OAI.HigherDimensionalBallPacking.Rigidity.lineHomotopy`, `OAI.HigherDimensionalBallPacking.Rigidity.standardJ`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Ambient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.COne`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Holder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.JetAmbient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Pairs` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cValue` (definitions bundle `OAIQ240Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedCurve` (definitions bundle `OAIQ240Bp011` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.clcInst1` and `OAI.HigherDimensionalBallPacking.Rigidity.clcInst2` (definitions bundle `OAIQ240Bp021` of this split); `OAI.HigherDimensionalBallPacking.Phase` and `OAI.HigherDimensionalBallPacking.capacity` (the published bundle `Def_BallPacking`).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_zeroSet_compact_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/ResidualCauchy.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.completed_line_closed)

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp021

section

attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
open HolderCompletion
variable {n : ℕ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.clcInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.clcInst2
local instance clcInst3_rd5f746_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance clcInst4_rd5f746_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
lemma completed_line_closed_bp240 {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1) (hout : ∀ x,S < capacity x →J x=standardJ n)
    {p q : Phase n} (hpq : p≠q) {t : ℕ → ℝ} (ht : ∀ i,t i∈Icc (0:ℝ) 1)
    {s : ℝ} (hs : Tendsto t atTop (𝓝 s))
    {w : ℕ → COne ℂ (Phase n)} {v : COne ℂ (Phase n)} (hw : Tendsto w atTop (𝓝 v))
    (hw0 : ∀ i,cValue (w i) 0=0)
    (hu : ∀ i,AffineLineCurve (lineHomotopy J (t i)) p q (markedCurve p q (w i))) :
    AffineLineCurve (lineHomotopy J s) p q (markedCurve p q v) := by
  sorry

end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
open HolderCompletion

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end
