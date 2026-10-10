-- Prove2me | Theorems.Thm_LandauFunction_landau_log_tendsto
-- name    : LandauFunction.landau_log_tendsto
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:34:07.295573+00:00
-- url     : https://prove2.me/theorems/c124029a-4d8d-4340-8034-e6c08ab78f61
-- title:
--   Landau's theorem: $\ln g(n)\sim\sqrt{n\ln n}$
-- statement:
--   Landau's function satisfies
--
--   $$\lim_{n\to\infty}\frac{\ln g(n)}{\sqrt{n\ln n}}=1,$$
--
--   equivalently $g(n)=e^{(1+o(1))\sqrt{n\ln n}}$.
--
--   This determines the growth rate of the largest order of an element of the symmetric group $S_n$.
--
--   **Formalization Note** The limit is along $n\to\infty$ in $\mathbb N$; at $n=0,1$ the denominator is $0$ and Lean's division gives $0$, which does not affect the limit.
-- source:
--   E. Landau (1902/1903); as quoted in Wikipedia, "Landau's function", revision oldid=1303222269 (https://en.wikipedia.org/w/index.php?title=Landau%27s_function&oldid=1303222269), third paragraph, first display, ref. [2].

import Mathlib
import Definitions.Def_LandauFunction_landau

namespace LandauFunction
theorem landau_log_tendsto :
    Filter.Tendsto (fun n : ℕ => Real.log (landau n) / Real.sqrt (n * Real.log n))
      Filter.atTop (nhds 1) := by sorry
end LandauFunction
