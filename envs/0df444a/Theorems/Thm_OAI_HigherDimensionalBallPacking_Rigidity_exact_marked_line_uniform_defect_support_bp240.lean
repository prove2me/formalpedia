-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_exact_marked_line_uniform_defect_support_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_uniform_defect_support_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:53:06.006174+00:00
-- url     : https://prove2.me/theorems/a4c77a19-9c24-48d4-a518-b6ab5f67268a
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_uniform_defect_support_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_uniform_defect_support` of [lean/OAI/Geometry/BallPacking/Compactness/MarkedCurves.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/MarkedCurves.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity`, with `open scoped ContDiff Topology`, `open Set Function Filter MeasureTheory`, `open scoped BoundedContinuousFunction`, `open HolderCompletion`):
--
--   ```lean
--   theorem exact_marked_line_uniform_defect_support_bp240 {J : Phase n → End n}
--       (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
--       (hJc : HasCompactSupport (fun x => J x-standardJ n))
--       {S T : ℝ} (hST : S<T) (hT : T<1)
--       (hout : ∀ x,S < capacity x →J x=standardJ n)
--       (p q : Phase n) (hpq : p≠q) :
--       ∃ R : ℝ,0<R ∧ ∀ t∈Icc (0:ℝ) 1,∀ (u : ℂ → Phase n),
--         AffineLineCurve (lineHomotopy J t) p q u →∀ c : ℂ,R<‖c‖ →
--           lineHomotopy J t (u c)=standardJ n ∧ HolderCompletion.geometricResidual u c=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.AffineLineCurve`, `OAI.HigherDimensionalBallPacking.Rigidity.Compatible`, `OAI.HigherDimensionalBallPacking.Rigidity.End`, `OAI.HigherDimensionalBallPacking.Rigidity.lineHomotopy` and `OAI.HigherDimensionalBallPacking.Rigidity.standardJ` (definitions bundle `OAIQ240Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.geometricResidual` (definitions bundle `OAIQ240Bp017` of this split); `OAI.HigherDimensionalBallPacking.Phase` and `OAI.HigherDimensionalBallPacking.capacity` (the published bundle `Def_BallPacking`).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_zeroSet_compact_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/MarkedCurves.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_uniform_defect_support)

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp017

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
open Set Function Filter MeasureTheory
open scoped BoundedContinuousFunction
open HolderCompletion
variable {n : ℕ}

theorem exact_marked_line_uniform_defect_support_bp240 {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x,S < capacity x →J x=standardJ n)
    (p q : Phase n) (hpq : p≠q) :
    ∃ R : ℝ,0<R ∧ ∀ t∈Icc (0:ℝ) 1,∀ (u : ℂ → Phase n),
      AffineLineCurve (lineHomotopy J t) p q u →∀ c : ℂ,R<‖c‖ →
        lineHomotopy J t (u c)=standardJ n ∧ HolderCompletion.geometricResidual u c=0 := by
  sorry

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end
