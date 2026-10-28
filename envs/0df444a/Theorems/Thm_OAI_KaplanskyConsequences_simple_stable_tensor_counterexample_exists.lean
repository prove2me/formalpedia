-- Prove2me | Theorems.Thm_OAI_KaplanskyConsequences_simple_stable_tensor_counterexample_exists
-- name    : OAI.KaplanskyConsequences.simple_stable_tensor_counterexample_exists
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T15:25:35.658685+00:00
-- url     : https://prove2.me/theorems/c8214a86-1c46-4576-b753-1e1b9e52c7fa
-- title:
--   OAI.KaplanskyConsequences.simple_stable_tensor_counterexample_exists (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KaplanskyConsequences.stable_finiteness_bundle`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KaplanskyConsequences.simple_stable_tensor_counterexample_exists` of [lean/OAI/Analysis/Kaplansky/Kaplansky/StableFiniteness/SimpleTensor.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/StableFiniteness/SimpleTensor.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KaplanskyConsequences`):
--
--   ```lean
--   theorem simple_stable_tensor_counterexample_exists : SimpleStableTensorCounterexample
--   ```
--
--   **Definitions.** The statement is written with `OAI.KaplanskyConsequences.SimpleStableTensorCounterexample` (the published bundle `Def_KaplanskyStableFiniteness`).
--
--   **Used by.** The proof of `OAI.KaplanskyConsequences.stable_finiteness_bundle` of this split imports it.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/StableFiniteness/SimpleTensor.lean (declaration OAI.KaplanskyConsequences.simple_stable_tensor_counterexample_exists)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyStableFiniteness

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace KaplanskyConsequences

theorem simple_stable_tensor_counterexample_exists : SimpleStableTensorCounterexample := by
  sorry

end KaplanskyConsequences
end
end

end OAI
end
