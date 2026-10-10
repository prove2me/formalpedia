-- Prove2me | Theorems.Thm_LandauFunction_landau_le_exp_div_e
-- name    : LandauFunction.landau_le_exp_div_e
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:32:51.555985+00:00
-- url     : https://prove2.me/theorems/23c84a13-24c0-48eb-a379-95c6481e1671
-- title:
--   $g(n)\le e^{n/e}$, with equality only at $n=0$
-- statement:
--   For every natural number $n$,
--
--   $$g(n)\le e^{n/e},$$
--
--   and equality holds if and only if $n=0$.
--
--   This is an elementary explicit upper bound valid for all $n$, weaker asymptotically than Landau's theorem.
-- source:
--   Wikipedia, "Landau's function", revision oldid=1303222269 (https://en.wikipedia.org/w/index.php?title=Landau%27s_function&oldid=1303222269), sentence "It can be shown that g(n) ≤ e^{n/e} with the only equality between the functions at n = 0".

import Mathlib
import Definitions.Def_LandauFunction_landau

namespace LandauFunction
theorem landau_le_exp_div_e (n : ℕ) :
    (landau n : ℝ) ≤ Real.exp (n / Real.exp 1) ∧
      ((landau n : ℝ) = Real.exp (n / Real.exp 1) ↔ n = 0) := by sorry
end LandauFunction
