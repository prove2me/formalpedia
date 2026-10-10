-- Prove2me | Theorems.Thm_LandauFunction_landau_initial_values
-- name    : LandauFunction.landau_initial_values
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:28:00.919978+00:00
-- url     : https://prove2.me/theorems/0992cba2-5271-4b3d-98e2-d7310072a705
-- title:
--   Initial values of Landau's function (OEIS A000793)
-- statement:
--   The first values of Landau's function are
--
--   $$g(0)=1,\ g(1)=1,\ g(2)=2,\ g(3)=3,\ g(4)=4,\ g(5)=6,\ g(6)=6,\ g(7)=12,\ g(8)=15.$$
--
--   For instance $5=2+3$ with $\operatorname{lcm}(2,3)=6$, realised in $S_5$ by $(1\,2)(3\,4\,5)$, and no partition of $5$ has a larger lcm. These values are the start of OEIS sequence A000793 and serve as a sanity check on the definition.
-- source:
--   Wikipedia, "Landau's function", revision oldid=1303222269 (https://en.wikipedia.org/w/index.php?title=Landau%27s_function&oldid=1303222269), third paragraph ("The integer sequence g(0) = 1, …, g(8) = 15"); also the example g(5) = g(6) = 6 in the second paragraph.

import Mathlib
import Definitions.Def_LandauFunction_landau

namespace LandauFunction
theorem landau_initial_values :
    landau 0 = 1 ∧ landau 1 = 1 ∧ landau 2 = 2 ∧ landau 3 = 3 ∧ landau 4 = 4 ∧
      landau 5 = 6 ∧ landau 6 = 6 ∧ landau 7 = 12 ∧ landau 8 = 15 := by sorry
end LandauFunction
