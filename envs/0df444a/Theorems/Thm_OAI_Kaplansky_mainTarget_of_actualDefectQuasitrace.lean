-- Prove2me | Theorems.Thm_OAI_Kaplansky_mainTarget_of_actualDefectQuasitrace
-- name    : OAI.Kaplansky.mainTarget_of_actualDefectQuasitrace
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T08:52:06.326021+00:00
-- url     : https://prove2.me/theorems/7e48877a-ed43-45c5-95ed-c95d14ae2c3c
-- title:
--   OAI.Kaplansky.mainTarget_of_actualDefectQuasitrace: intermediate lemma from OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kaplansky.kaplansky_quasitrace_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Kaplansky.mainTarget_of_actualDefectQuasitrace` of [lean/OAI/Analysis/Kaplansky/Kaplansky/ActualAlgebra.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/ActualAlgebra.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kaplansky`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem mainTarget_of_actualDefectQuasitrace
--       (hq : ∃ τ : OneQuasitrace ActualDefectAlgebra, τ.Normalized ∧ τ.IsTwo) : MainTarget
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kaplansky.ActualDefectAlgebra` (definitions bundle `OAIQ4Kq009` of this split); `OAI.Kaplansky.actualDefectAlgebra_cstar` (definitions bundle `OAIQ4Kq011` of this split); `OAI.Kaplansky.MainTarget`, `OAI.Kaplansky.OneQuasitrace`, `OAI.Kaplansky.OneQuasitrace.IsTwo` and `OAI.Kaplansky.OneQuasitrace.Normalized` (the published bundle `Def_KaplanskyQuasitrace`).
--
--   **Used by.** The proof of `OAI.Kaplansky.kaplansky_quasitrace_counterexample` of this split imports it.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/ActualAlgebra.lean (declaration OAI.Kaplansky.mainTarget_of_actualDefectQuasitrace)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyQuasitrace
import Definitions.Def_OAIQ4Kq011

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

section
open scoped BigOperators
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

theorem mainTarget_of_actualDefectQuasitrace
    (hq : ∃ τ : OneQuasitrace ActualDefectAlgebra, τ.Normalized ∧ τ.IsTwo) : MainTarget := by
  sorry

end

end Kaplansky

end

end OAI
end
