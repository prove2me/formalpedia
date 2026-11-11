-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_compatibleFrame_inverse_left_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame_inverse_left_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:08:48.646062+00:00
-- url     : https://prove2.me/theorems/7d972ffb-6bd1-4ba1-8f4e-bcfc3310e24f
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame_inverse_left_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame_inverse_left` of [lean/OAI/Geometry/BallPacking/Compactness/JetCauchy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/JetCauchy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion`, with `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Filter`):
--
--   ```lean
--   lemma compatibleFrame_inverse_left_bp240 {J : End n} (hJ : Compatible J) (v : Phase n) :
--       (compatibleFrame J).inverse (compatibleFrame J v) = v
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.Compatible` and `OAI.HigherDimensionalBallPacking.Rigidity.End` (definitions bundle `OAIQ240Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame` (definitions bundle `OAIQ240Bp006` of this split); `OAI.HigherDimensionalBallPacking.Phase` (the published bundle `Def_BallPacking`).
--
--   **Used by.** The proofs of `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_add_compact_fredholm_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.equicontinuous_CR_derivative_bound_bp240` and `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_local_jet_cauchy_bp240` of this split import it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/JetCauchy.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame_inverse_left)

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
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {n : ℕ}

lemma compatibleFrame_inverse_left_bp240 {J : End n} (hJ : Compatible J) (v : Phase n) :
    (compatibleFrame J).inverse (compatibleFrame J v) = v := by
  sorry

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end
