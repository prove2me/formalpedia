-- Prove2me | Theorems.Thm_LandauFunction_landau_log_asymptotic_expansion
-- name    : LandauFunction.landau_log_asymptotic_expansion
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:29.465202+00:00
-- url     : https://prove2.me/theorems/1e4b08b2-2b3a-4123-9c1d-3b2a232717bb
-- title:
--   Three-term asymptotic expansion of $\ln g(n)$ (Massias–Nicolas–Robin 1988)
-- statement:
--   As $n\to\infty$,
--
--   $$\ln g(n)=\sqrt{n\ln n}\left(1+\frac{\ln\ln n-1}{2\ln n}-\frac{(\ln\ln n)^2-6\ln\ln n+9}{8(\ln n)^2}+O\!\left(\left(\frac{\ln\ln n}{\ln n}\right)^{3}\right)\right).$$
--
--   This refines Landau's theorem $\ln g(n)\sim\sqrt{n\ln n}$ by two further terms.
--
--   **Formalization Note** The statement is that the difference between $\ln g(n)$ and the explicit main term is $O\bigl(\sqrt{n\ln n}\,(\ln\ln n/\ln n)^3\bigr)$ along $n\to\infty$ in $\mathbb N$.
-- source:
--   Massias, Nicolas, Robin, Acta Arith. 50 (1988) 221–242; as quoted in Wikipedia, "Landau's function", revision oldid=1303222269 (https://en.wikipedia.org/w/index.php?title=Landau%27s_function&oldid=1303222269), display after "More precisely", ref. [3].

import Mathlib
import Definitions.Def_LandauFunction_landau

namespace LandauFunction
theorem landau_log_asymptotic_expansion :
    (fun n : ℕ => Real.log (landau n) - Real.sqrt (n * Real.log n) *
        (1 + (Real.log (Real.log n) - 1) / (2 * Real.log n)
          - (Real.log (Real.log n) ^ 2 - 6 * Real.log (Real.log n) + 9) / (8 * Real.log n ^ 2)))
      =O[Filter.atTop]
      (fun n : ℕ => Real.sqrt (n * Real.log n) * (Real.log (Real.log n) / Real.log n) ^ 3) := by
  sorry
end LandauFunction
