-- Prove2me | Theorems.Thm_NisanRonen_Rounding_encodedAllocation_output_polytime
-- name    : NisanRonen.Rounding.encodedAllocation_output_polytime
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T05:55:26.014159+00:00
-- url     : https://prove2.me/theorems/2fac1919-c841-551e-80df-1114539a4136
-- title:
--   Polynomial-time conversion from framed binary allocations to machine symbols
-- statement:
--   For a fixed positive number of machines, a Mathlib TM2 reads the framed unary list encoding of an allocation and writes the same allocation using one machine symbol per task. The time bound is polynomial in the length of the framed input.
-- source:
--   Nisan and Ronen (2001), Algorithmic Mechanism Design, §5.6, p. 192, https://doi.org/10.1006/game.1999.0790. TM2 implementation of the rounded scheduling algorithm.

import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_NisanRonen_Rounding_checkedColumns

namespace NisanRonen.Rounding
theorem encodedAllocation_output_polytime (n : ℕ) [NeZero n] :
    Nonempty (Turing.TM2ComputableInPolyTime
      (Turing.MultiTapeTM.encList (encAgent n))
      (id : List (Fin n) → List (Fin n)) (id : List (Fin n) → List (Fin n))) := by sorry
end NisanRonen.Rounding
