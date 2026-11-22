-- Prove2me | Theorems.Thm_K230_seed230_iff_thm
-- name    : K230.seed230_iff_thm
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T21:15:19.605355+00:00
-- url     : https://prove2.me/theorems/0f04193a-d187-46e4-8c88-dd1742b7a58e
-- title:
--   K230: seeded search halting iff the falsity code is derivable
-- statement:
--   The abstract proof enumerator halts from `seed230` if and only if the falsity code $1$ is derivable in the numerical calculus `Thm230`. This is `seed230_iff_thm` in `Seed230.v` (soundness and completeness of the search from the actual initial state).
-- source:
--   https://github.com/elliotglazer/k230-rocq/blob/main/coq/logic/Seed230.v

import Definitions.Def_K230_enum
import Definitions.Def_K230_calculus

namespace K230
theorem seed230_iff_thm : haltsFrom seed230 ↔ Thm230 1 := by sorry
end K230
