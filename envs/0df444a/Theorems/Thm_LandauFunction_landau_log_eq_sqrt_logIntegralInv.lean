-- Prove2me | Theorems.Thm_LandauFunction_landau_log_eq_sqrt_logIntegralInv
-- name    : LandauFunction.landau_log_eq_sqrt_logIntegralInv
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:31:30.431802+00:00
-- url     : https://prove2.me/theorems/f3a3ea36-d9a9-4b9a-890c-1428661d98ee
-- title:
--   $\ln g(n)=\sqrt{\mathrm{Li}^{-1}(n)}+O(R(\sqrt{n\ln n})\ln n)$ (Massias–Nicolas–Robin 1988)
-- statement:
--   Let $c>0$ and put $R(x)=x\exp\!\left(-c(\ln x)^{3/5}(\ln\ln x)^{-1/5}\right)$. If $\pi(x)-\mathrm{Li}(x)=O(R(x))$ as $x\to\infty$, then, as $n\to\infty$,
--
--   $$\ln g(n)=\sqrt{\mathrm{Li}^{-1}(n)}+O\!\left(R\bigl(\sqrt{n\ln n}\bigr)\ln n\right).$$
--
--   Combined with Ford's error term this holds unconditionally for some $c>0$; it expresses $\ln g(n)$ through the inverse logarithmic integral.
--
--   **Formalization Note** The hypothesis on $\pi-\mathrm{Li}$ is stated with the same $c$ as the conclusion, as in the source; $R$ is written out explicitly in both places.
-- source:
--   Massias, Nicolas, Robin, Acta Arith. 50 (1988) 221–242; as quoted in Wikipedia, "Landau's function", revision oldid=1303222269 (https://en.wikipedia.org/w/index.php?title=Landau%27s_function&oldid=1303222269), display "ln g(n) = sqrt(Li^{-1}(n)) + O(R(sqrt(n ln n)) ln n)", ref. [3].

import Mathlib
import Definitions.Def_LandauFunction_landau
import Definitions.Def_LandauFunction_logIntegral

namespace LandauFunction
theorem landau_log_eq_sqrt_logIntegralInv (c : ℝ) (hc : 0 < c)
    (hπ : (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) - logIntegral x) =O[Filter.atTop]
      (fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((3 : ℝ) / 5) *
        Real.log (Real.log x) ^ (-(1 : ℝ) / 5)))) :
    (fun n : ℕ => Real.log (landau n) - Real.sqrt (logIntegralInv n)) =O[Filter.atTop]
      (fun n : ℕ =>
        (Real.sqrt (n * Real.log n) *
          Real.exp (-c * Real.log (Real.sqrt (n * Real.log n)) ^ ((3 : ℝ) / 5) *
            Real.log (Real.log (Real.sqrt (n * Real.log n))) ^ (-(1 : ℝ) / 5))) *
        Real.log n) := by sorry
end LandauFunction
