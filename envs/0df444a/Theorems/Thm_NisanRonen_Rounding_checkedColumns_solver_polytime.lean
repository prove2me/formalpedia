-- Prove2me | Theorems.Thm_NisanRonen_Rounding_checkedColumns_solver_polytime
-- name    : NisanRonen.Rounding.checkedColumns_solver_polytime
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T05:55:08.153989+00:00
-- url     : https://prove2.me/theorems/54259283-9c8c-5a9f-8323-3a89c4d59606
-- title:
--   Polynomial-time bounded load-vector scheduling in framed encodings
-- statement:
--   For a fixed number of machines and a fixed cap, the bounded load-vector dynamic program on checked columns is polynomial-time computable by a Mathlib TM2. The input is the framed binary encoding of a list of column checks, and the output is a framed unary list of machine indices. A missing column yields the empty allocation.
-- source:
--   Nisan and Ronen (2001), Algorithmic Mechanism Design, §5.6, p. 192, https://doi.org/10.1006/game.1999.0790. TM2 implementation of the rounded scheduling algorithm.

import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_NisanRonen_Rounding_checkedColumns

namespace NisanRonen.Rounding
theorem checkedColumns_solver_polytime (n cap : ℕ) :
    Nonempty (Turing.TM2ComputableInPolyTime encCheckedColumns
      (Turing.MultiTapeTM.encList (encAgent n)) (solveCheckedColumns n cap)) := by sorry
end NisanRonen.Rounding
