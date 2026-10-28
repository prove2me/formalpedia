-- Prove2me | Theorems.Thm_OAI_Kaplansky_retainedGrouped_no_test_frame
-- name    : OAI.Kaplansky.retainedGrouped_no_test_frame
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T15:34:55.57639+00:00
-- url     : https://prove2.me/theorems/03e4e886-3615-4f32-bb72-3b209b978081
-- title:
--   OAI.Kaplansky.retainedGrouped_no_test_frame: intermediate lemma from OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KaplanskyConsequences.stable_finiteness_bundle`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Kaplansky.retainedGrouped_no_test_frame` of [lean/OAI/Analysis/Kaplansky/BundleTests/Obstruction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/BundleTests/Obstruction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kaplansky`, with `open Bundle Topology`, `open ComplexGrassmann`):
--
--   ```lean
--   theorem retainedGrouped_no_test_frame {m R : ℕ} (hm : 0 < m) (hR : 0 < R) :
--       IsEmpty (ContinuousOrthonormalStageFrame (retainedGroupedStage m R) (2*m*testRank m R 0))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kaplansky.testProjectiveDimension` and `OAI.Kaplansky.testRank` (definitions bundle `OAIQ15Sf000` of this split); `OAI.Kaplansky.ContinuousOrthonormalStageFrame` (definitions bundle `OAIQ15Sf007` of this split); `OAI.Kaplansky.retainedGroupedStage` (definitions bundle `OAIQ15Sf010` of this split).
--
--   **Used by.** The proof of `OAI.Kaplansky.actualAlgebra_matrix_not_properlyInfinite` of this split imports it.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/BundleTests/Obstruction.lean (declaration OAI.Kaplansky.retainedGrouped_no_test_frame)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ15Sf010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

theorem retainedGrouped_no_test_frame {m R : ℕ} (hm : 0 < m) (hR : 0 < R) :
    IsEmpty (ContinuousOrthonormalStageFrame (retainedGroupedStage m R) (2*m*testRank m R 0)) := by
  sorry

end Kaplansky

end

end OAI
end
