-- Prove2me | Theorems.Thm_LandauFunction_landau_le_massias
-- name    : LandauFunction.landau_le_massias
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:33:36.062967+00:00
-- url     : https://prove2.me/theorems/d7968b68-23aa-4a19-8088-26b985834ae5
-- title:
--   Massias' bound $g(n)\le\exp(1.05314\sqrt{n\ln n})$
-- statement:
--   For every natural number $n$,
--
--   $$g(n)\le\exp\!\left(1.05314\sqrt{n\ln n}\right).$$
--
--   This makes the upper half of Landau's theorem explicit, with a constant close to the asymptotically optimal value $1$.
--
--   **Formalization Note** For $n=0,1$ the right-hand side is $1=g(n)$.
-- source:
--   J.-P. Massias, Ann. Fac. Sci. Toulouse Math. (5) 6 (1984) 269–281; as quoted in Wikipedia, "Landau's function", revision oldid=1303222269 (https://en.wikipedia.org/w/index.php?title=Landau%27s_function&oldid=1303222269), last display, ref. [5].

import Mathlib
import Definitions.Def_LandauFunction_landau

namespace LandauFunction
theorem landau_le_massias (n : ℕ) :
    (landau n : ℝ) ≤ Real.exp (1.05314 * Real.sqrt (n * Real.log n)) := by sorry
end LandauFunction
