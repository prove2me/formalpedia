-- Prove2me | Theorems.Thm_NisanRonen_Rounding_unitMakespan_polytime
-- name    : NisanRonen.Rounding.unitMakespan_polytime
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:03:47.205046+00:00
-- url     : https://prove2.me/theorems/30439775-2d68-416a-93af-449e7ca16710
-- title:
--   The rounded bonus makespan in grid units is polynomial-time computable
-- statement:
--   For each fixed machine count, a Mathlib TM2 computes the integer makespan of an allocation in time polynomial in the binary encoding length. It reads the task columns in grid units and a list assigning machines to tasks. It sums the processing times associated with each machine and returns the largest sum in binary. As in the specified function, inputs of unequal list lengths use only their paired prefix.
-- source:
--   Nisan and Ronen (2001), Algorithmic Mechanism Design, Theorem 5.9 and Definition 34, p. 193, https://doi.org/10.1006/game.1999.0790. The polynomial-time computation of the bonus makespan in grid units.

import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_NisanRonen_Rounding_encodeInstanceAlloc
import Definitions.Def_NisanRonen_Rounding_unitMakespan

namespace NisanRonen.Rounding
theorem unitMakespan_polytime (n : ℕ) :
    Nonempty (Turing.TM2ComputableInPolyTime (encodeInstanceAlloc (n := n))
      Computability.encodeNat (unitMakespan (n := n))) := by sorry
end NisanRonen.Rounding
