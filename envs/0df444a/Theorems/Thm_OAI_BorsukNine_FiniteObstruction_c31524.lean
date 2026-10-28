-- Prove2me | Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c31524
-- name    : OAI.BorsukNine.FiniteObstruction.c31524
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:46:18.451449+00:00
-- url     : https://prove2.me/theorems/444b1481-d88c-4e7e-99c2-357c5e82967a
-- title:
--   OAI.BorsukNine.FiniteObstruction.c31524: intermediate lemma from OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion (result family 156)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BorsukNine.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A nine-dimensional counterexample to Borsuk's covering assertion (result family 156)*, OpenAI Math Release, September 23, 2026, result family 156, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BorsukNine.FiniteObstruction.c31524` of [lean/OAI/Geometry/Borsuk/FiniteCases/Cases101.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Borsuk/FiniteCases/Cases101.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BorsukNine.FiniteObstruction`, with `open Set MeasureTheory`):
--
--   ```lean
--   theorem c31524 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
--       Q {1, 2, 3, 9} → ¬ Q {0, 3, 7, 9} → Q {3, 4, 7, 9} → False
--   ```
--
--   **Definitions.** The statement is written with `OAI.BorsukNine.FiniteObstruction.Family`, `OAI.BorsukNine.FiniteObstruction.Labels` and `OAI.BorsukNine.FiniteObstruction.TenSystem` (definitions bundle `OAIQ058B000` of this split).
--
--   **Used by.** The proofs of `OAI.BorsukNine.FiniteObstruction.c32601`, `OAI.BorsukNine.FiniteObstruction.c32606`, `OAI.BorsukNine.FiniteObstruction.c32611`, `OAI.BorsukNine.FiniteObstruction.c32621`, `OAI.BorsukNine.FiniteObstruction.c32630`, `OAI.BorsukNine.FiniteObstruction.c32662`, `OAI.BorsukNine.FiniteObstruction.c32668`, `OAI.BorsukNine.FiniteObstruction.c32671`, `OAI.BorsukNine.FiniteObstruction.c32689`, `OAI.BorsukNine.FiniteObstruction.c32696`, `OAI.BorsukNine.FiniteObstruction.c32711`, `OAI.BorsukNine.FiniteObstruction.c32712`, `OAI.BorsukNine.FiniteObstruction.c32720`, `OAI.BorsukNine.FiniteObstruction.c32728`, `OAI.BorsukNine.FiniteObstruction.c32742`, `OAI.BorsukNine.FiniteObstruction.c32778`, `OAI.BorsukNine.FiniteObstruction.c32780`, `OAI.BorsukNine.FiniteObstruction.c32784`, `OAI.BorsukNine.FiniteObstruction.c32786`, `OAI.BorsukNine.FiniteObstruction.c32795`, `OAI.BorsukNine.FiniteObstruction.c32804`, `OAI.BorsukNine.FiniteObstruction.c32813`, `OAI.BorsukNine.FiniteObstruction.c32815` and `OAI.BorsukNine.FiniteObstruction.no_ten_system` of this split import it.
-- source:
--   OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion (result family 156), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 156; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-nine-dimensional-counterexample-to-Borsuks-covering-assertion-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Borsuk/FiniteCases/Cases101.lean (declaration OAI.BorsukNine.FiniteObstruction.c31524)

import Mathlib
import Definitions.Def_OAIQ058B000

section

attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31524 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 2, 3, 9} → ¬ Q {0, 3, 7, 9} → Q {3, 4, 7, 9} → False := by
  sorry

end BorsukNine.FiniteObstruction

end OAI
end
