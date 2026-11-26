-- Prove2me | Theorems.Thm_NisanRonen_Rounding_checkedColumns_input_polytime
-- name    : NisanRonen.Rounding.checkedColumns_input_polytime
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T05:55:22.377856+00:00
-- url     : https://prove2.me/theorems/7fa6819f-1905-498f-95f1-4749e66cc2d7
-- title:
--   Polynomial-time input conversion for bounded scheduling
-- statement:
--   For a fixed machine count and a fixed cap, a Mathlib TM2 reads the binary encoding of a rounded instance and writes its checked columns in framed binary form. A column is written as missing if any of its entries exceeds the cap. The machine runs in polynomial time in the length of the original encoding.
-- source:
--   Nisan and Ronen (2001), Algorithmic Mechanism Design, §5.6, p. 192, https://doi.org/10.1006/game.1999.0790. TM2 implementation of the rounded scheduling algorithm.

import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_NisanRonen_Rounding_checkedColumns
import Definitions.Def_NisanRonen_Rounding_encodeInstance

namespace NisanRonen.Rounding
theorem checkedColumns_input_polytime (n cap : ℕ) :
    Nonempty (Turing.TM2ComputableInPolyTime (encodeInstance (n := n)) encCheckedColumns
      (fun cols => cols.map (checkColumn cap))) := by sorry
end NisanRonen.Rounding
