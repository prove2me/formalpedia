-- Prove2me | Theorems.Thm_K230_tm230_rm
-- name    : K230.tm230_rm
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T21:14:40.260181+00:00
-- url     : https://prove2.me/theorems/9e3ca9f9-007c-4bce-b09d-3b3af4dc4ad7
-- title:
--   K230: TM halting iff register program halting
-- statement:
--   The frozen 230-state Turing machine halts from the blank tape if and only if the compiled register program `p230`, started with empty instruction pointer and initial registers `R0`, reaches its halt leaf. This is `tm230_rm` in `Sim230Main.v`, the simulation equivalence between the literal transition table and the register program.
-- source:
--   https://github.com/elliotglazer/k230-rocq/blob/main/coq/tm/Sim230Main.v

import Definitions.Def_K230_tm
import Definitions.Def_K230_rm
import Definitions.Def_K230_prog

namespace K230
theorem tm230_rm : Halts c0 ↔ rmHalts p230 ([], R0) := by sorry
end K230
