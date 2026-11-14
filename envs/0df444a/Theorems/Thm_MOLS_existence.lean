-- Prove2me | Theorems.Thm_MOLS_existence
-- name    : MOLS.existence
-- status  : Open
-- author  : @parclytaxel
-- created : 2026-11-13T11:05:22.76821+00:00
-- url     : https://prove2.me/theorems/c1bb3901-9c2e-45c3-b965-b796c0d740e7
-- title:
--   Existence of mutually orthogonal Latin squares
-- statement:
--   Mutually orthogonal Latin squares exist iff $n\ne2,6$.
-- source:
--   R. C. Bose, S. S. Shrikhande, and E. T. Parker, “Further Results on the Construction of Mutually Orthogonal Latin Squares and the Falsity of Euler’s Conjecture,” Canadian Journal of Mathematics, vol. 12, pp. 189–203, 1960. doi:10.4153/CJM-1960-016-5

import Definitions.Def_MOLS

namespace MOLS

theorem existence {n : ℕ} : Nonempty (MOLS n) ↔ n ≠ 2 ∧ n ≠ 6 := by
  sorry

end MOLS
