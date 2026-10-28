-- Prove2me | Theorems.Thm_OAI_ArExplicit_CocycleData_valid_true_z
-- name    : OAI.ArExplicit.CocycleData.valid_true_z
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T13:42:47.919914+00:00
-- url     : https://prove2.me/theorems/8ffead1f-3a05-4772-a190-6b185c141643
-- title:
--   OAI.ArExplicit.CocycleData.valid_true_z: one index of the cocycle certificate, from OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   The Boolean `certificate` evaluates to `true` at the index `(true, .z)` of `TIndex`. This is one of twenty finite checks that OpenAI's proof of `OAI.ArExplicit.Statement.main` carries out inside the Lean kernel: the statement and its proof are OpenAI's (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the private lemma `valid_true_z` of [lean/OAI/Algebra/AuslanderReiten/Cocycles/CocycleCertificate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/CocycleCertificate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a and published here as a statement of its own.
--
--   **The statement**, as published (namespace `OAI.ArExplicit.CocycleData`):
--
--   ```lean
--   theorem valid_true_z : certificate (true, .z) = true
--   ```
--
--   **Definitions.** `certificate` and the index type are in the definitions bundle `OAIQ031A000` of this split.
--
--   **Why it is a statement of its own.** All twenty checks in one file exceeded the verifier's 300 s limit, so each is published separately.
--
--   **Used by.** The proof of `OAI.ArExplicit.CocycleData.certificate_valid` of this split imports it.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/CocycleCertificate.lean (declaration OAI.ArExplicit.CocycleData.valid_true_z)

import Mathlib
import Definitions.Def_OAIQ031A000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.CocycleData

theorem valid_true_z : certificate (true, .z) = true := by
  sorry

end ArExplicit.CocycleData

end OAI
end
