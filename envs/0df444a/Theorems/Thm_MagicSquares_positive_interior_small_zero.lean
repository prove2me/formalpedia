-- Prove2me | Theorems.Thm_MagicSquares_positive_interior_small_zero
-- name    : MagicSquares.positive_interior_small_zero
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-21T21:01:22.631565+00:00
-- url     : https://prove2.me/theorems/fbe7af10-42ac-48a5-ae22-a565eb27792c
-- title:
--   Positive semi-magic squares vanish below the order
-- statement:
--   Let n >= 1 and t < n. Then there are no semi-magic squares of order n and line sum t with every entry strictly positive.
--
--   In symbols,
--
--   $$I_{n}(t) = 0.$$
--
--   Each row contains n entries, each at least one, so any such square has line sum at least n. Hence the interior count vanishes below the order. These are exactly the interior lattice points of the dilate t * B_{n} of the Birkhoff polytope, so this says the dilate has no interior lattice points before the codegree.
--
--   **Formalization Note** Lean counts via positiveInteriorCount, the card of the filtered finset over Square n (Fin (t+1)) with positivity 1 <= (M i j : Nat).
-- source:
--   R. P. Stanley, Duke Math. J. 40 (1973), 607--632, interior points of dilates of the Birkhoff polytope; M. Beck, M. Cohen, J. Cuomo and P. Gribelyuk, Amer. Math. Monthly 110 (2003), 707--717 (arXiv:math/0201013).

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquares_positiveInteriorCount
open MagicSquares

namespace MagicSquares

theorem positive_interior_small_zero (n t : Nat) (hn : 1 <= n) (htn : t < n) :
    positiveInteriorCount n t = 0 := by sorry

end MagicSquares
