-- Prove2me | Theorems.Thm_OAI_ArExplicit_CocycleData_certificate_valid
-- name    : OAI.ArExplicit.CocycleData.certificate_valid
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T13:01:05.807131+00:00
-- url     : https://prove2.me/theorems/5f46c880-27d2-420c-9d96-11de9c2a44ba
-- title:
--   OAI.ArExplicit.CocycleData.certificate_valid: the cocycle certificate holds at every index, from OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   For every index `a` of the finite index type `TIndex`, the Boolean `certificate a` evaluates to `true`. This is a finite check that OpenAI's proof of `OAI.ArExplicit.Statement.main` carries out inside the Lean kernel: the statement and its proof are OpenAI's (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ArExplicit.CocycleData.certificate_valid` of [lean/OAI/Algebra/AuslanderReiten/Cocycles/CocycleCertificate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/CocycleCertificate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ArExplicit.CocycleData`):
--
--   ```lean
--   theorem certificate_valid (a : TIndex) : certificate a = true
--   ```
--
--   **Definitions.** `TIndex` and `certificate` are in the definitions bundle `OAIQ031A000` of this split.
--
--   **Why it is a statement of its own.** A definitions bundle later in this split rests on this fact, and its proof runs twenty kernel computations (`decide +kernel`), which take a few minutes in total. Published as a statement, the bundle imports a cheap stub and the computation sits in one proof.
--
--   **Used by.** The definitions bundle `OAIQ031A005` of this split imports it.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/CocycleCertificate.lean (declaration OAI.ArExplicit.CocycleData.certificate_valid)

import Mathlib
import Definitions.Def_OAIQ031A000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.CocycleData

theorem certificate_valid (a : TIndex) : certificate a = true := by
  sorry

end ArExplicit.CocycleData

end OAI
end
