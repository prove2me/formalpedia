-- Prove2me | Theorems.Thm_NisanRonen_Rounding_boundedLoadDP_polytime
-- name    : NisanRonen.Rounding.boundedLoadDP_polytime
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T05:34:47.918153+00:00
-- url     : https://prove2.me/theorems/a42cef74-8156-5704-91f8-067316a60c99
-- title:
--   Polynomial TM2 implementation of the bounded load-vector dynamic program
-- statement:
--   For each fixed number of machines and each fixed cap, there is a polynomial-time Mathlib TM2 machine computing the bounded load-vector dynamic program. The machine reads a binary encoding of the task columns and writes the list of selected machines. On any input with an entry above the cap it writes the empty list. The time bound is a polynomial in the length of the encoded input with coefficients and degree allowed to depend on the machine count and cap.
-- source:
--   Nisan and Ronen (2001), Algorithmic Mechanism Design, §5.6, p. 192, https://doi.org/10.1006/game.1999.0790. The exact dynamic-programming step on the rounded instance.

import Definitions.Def_NisanRonen_Rounding_boundedLoadDP
import Definitions.Def_NisanRonen_Rounding_encodeInstance

namespace NisanRonen.Rounding

theorem boundedLoadDP_polytime (n cap : ℕ) :
    Nonempty (Turing.TM2ComputableInPolyTime (encodeInstance (n := n))
      (id : List (Fin n) → List (Fin n)) (boundedLoadDP (n := n) cap)) := by sorry

end NisanRonen.Rounding
