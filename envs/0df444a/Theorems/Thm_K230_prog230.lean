-- Prove2me | Theorems.Thm_K230_prog230
-- name    : K230.prog230
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T21:15:09.763507+00:00
-- url     : https://prove2.me/theorems/a789a27a-b05c-4ff2-93a1-2217614555b0
-- title:
--   K230: register program halting iff seeded search halting
-- statement:
--   The register program `p230` halts from `R0` if and only if the abstract six-register proof enumerator halts from its actual nonzero seed state `seed230`. This is `prog230` in `Main230.v`, connecting the compiled program to the abstract enumerator.
-- source:
--   https://github.com/elliotglazer/k230-rocq/blob/main/coq/prog/Main230.v

import Definitions.Def_K230_rm
import Definitions.Def_K230_prog
import Definitions.Def_K230_enum

namespace K230
theorem prog230 : rmHalts p230 ([], R0) ↔ haltsFrom seed230 := by sorry
end K230
