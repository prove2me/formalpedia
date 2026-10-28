-- Prove2me | Theorems.Thm_OAI_ThorpNine_Tail_Thorp_StrongTail_strong_tail_q77
-- name    : OAI.ThorpNine.Tail.Thorp.StrongTail.strong_tail_q77
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:52:44.225518+00:00
-- url     : https://prove2.me/theorems/1b43b001-6191-4b27-b141-a0b6c7417a3d
-- title:
--   OAI.ThorpNine.Tail.Thorp.StrongTail.strong_tail_q77: intermediate lemma from OpenAI, Optimal logarithmic mixing of the Thorp shuffle (routing densities)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ThorpNine.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Optimal logarithmic mixing of the Thorp shuffle (routing densities)*, OpenAI Math Release, September 26, 2026, result family 238, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ThorpNine.Tail.Thorp.StrongTail.strong_tail` of [lean/OAI/Probability/ThorpRouting/Tail/Main.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ThorpRouting/Tail/Main.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ThorpNine.Tail.Thorp.StrongTail`, with `open scoped BigOperators Classical`, `open Specht UnitaryFinite`):
--
--   ```lean
--   theorem strong_tail_q77 : MainStatement
--   ```
--
--   **Definitions.** The statement is written with `OAI.ThorpNine.Tail.Thorp.StrongTail.MainStatement` (the published bundle `Def_ThorpRouting`).
--
--   **Used by.** The proof of `OAI.ThorpNine.main` of this split imports it.
-- source:
--   OpenAI, Optimal logarithmic mixing of the Thorp shuffle (routing densities), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 238; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Routing-densities-and-representation-contraction-for-Thorp-sweeps-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ThorpRouting/Tail/Main.lean (declaration OAI.ThorpNine.Tail.Thorp.StrongTail.strong_tail)

import Mathlib
import Definitions.Def_ThorpRouting

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Tail

namespace Thorp.StrongTail
open scoped BigOperators Classical

open Specht UnitaryFinite

theorem strong_tail_q77 : MainStatement := by
  sorry

end Thorp.StrongTail

end ThorpNine.Tail

end OAI
end
