-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_exact_marked_zeroSet_compact_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_zeroSet_compact_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:57:58.022495+00:00
-- url     : https://prove2.me/theorems/26e03de3-a784-4f7d-ba41-20337e0fc19e
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_zeroSet_compact_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_zeroSet_compact` of [lean/OAI/Geometry/BallPacking/Compactness/ResidualCauchy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/ResidualCauchy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity`, with `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Filter`, `open HolderCompletion`):
--
--   ```lean
--   theorem exact_marked_zeroSet_compact_bp240 {J : Phase n → End n}
--       (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
--       (hJc : HasCompactSupport (fun x => J x-standardJ n))
--       {S T : ℝ} (hST : S<T) (hT : T<1) (hout : ∀ x,S < capacity x →J x=standardJ n)
--       {p q : Phase n} (hpq : p≠q) : IsCompact (exactMarkedZeroSet J p q)
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.Compatible`, `OAI.HigherDimensionalBallPacking.Rigidity.End`, `OAI.HigherDimensionalBallPacking.Rigidity.standardJ`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Ambient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.COne`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Holder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.JetAmbient` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Pairs` (definitions bundle `OAIQ240Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.exactMarkedZeroSet` (definitions bundle `OAIQ240Bp021` of this split); `OAI.HigherDimensionalBallPacking.Phase` and `OAI.HigherDimensionalBallPacking.capacity` (the published bundle `Def_BallPacking`).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.Rigidity.adapted_line_continuation_data_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/ResidualCauchy.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_zeroSet_compact)

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
namespace HigherDimensionalBallPacking.Rigidity

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
open HolderCompletion
variable {n : ℕ}

local instance empInst1_r9c7de3_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance empInst2_r9c7de3_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
theorem exact_marked_zeroSet_compact_bp240 {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1) (hout : ∀ x,S < capacity x →J x=standardJ n)
    {p q : Phase n} (hpq : p≠q) : IsCompact (exactMarkedZeroSet J p q) := by
  sorry

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end
