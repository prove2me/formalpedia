-- Prove2me | Theorems.Thm_LandauFunction_landau_riemann_hypothesis_iff
-- name    : LandauFunction.landau_riemann_hypothesis_iff
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:32:18.603767+00:00
-- url     : https://prove2.me/theorems/b7d58dda-135d-49e4-9dbf-b6852eed199d
-- title:
--   Riemann hypothesis criterion via Landau's function
-- statement:
--   The inequality
--
--   $$\ln g(n)<\sqrt{\mathrm{Li}^{-1}(n)}$$
--
--   holds for all sufficiently large $n$ if and only if the Riemann hypothesis is true.
--
--   This is an elementary reformulation of the Riemann hypothesis in terms of element orders in symmetric groups; it is included as a faithful statement of the source, not as an expected deliverable.
--
--   **Formalization Note** The Riemann hypothesis is Mathlib's `RiemannHypothesis`; $\mathrm{Li}$ is the offset logarithmic integral (using $\mathrm{li}$ instead changes $\mathrm{Li}^{-1}(n)$ by $O(\ln n)$).
-- source:
--   Massias, Nicolas, Robin, Acta Arith. 50 (1988); as quoted in Wikipedia, "Landau's function", revision oldid=1303222269 (https://en.wikipedia.org/w/index.php?title=Landau%27s_function&oldid=1303222269), sentence "The statement that ln g(n) < sqrt(Li^{-1}(n)) for all sufficiently large n is equivalent to the Riemann hypothesis".

import Mathlib
import Definitions.Def_LandauFunction_landau
import Definitions.Def_LandauFunction_logIntegral

namespace LandauFunction
theorem landau_riemann_hypothesis_iff :
    (∀ᶠ n : ℕ in Filter.atTop, Real.log (landau n) < Real.sqrt (logIntegralInv n)) ↔
      RiemannHypothesis := by sorry
end LandauFunction
