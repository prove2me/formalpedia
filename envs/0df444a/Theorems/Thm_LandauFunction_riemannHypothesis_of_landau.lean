-- Prove2me | Theorems.Thm_LandauFunction_riemannHypothesis_of_landau
-- name    : LandauFunction.riemannHypothesis_of_landau
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-20T23:53:42.584493+00:00
-- url     : https://prove2.me/theorems/deb30264-17d4-4824-9e58-f9bb596db881
-- title:
--   If $\ln g(n)<\sqrt{\mathrm{Li}^{-1}(n)}$ for all large $n$, then RH holds
-- statement:
--   Let $g(n)$ be Landau's function, the largest order of an element of the symmetric group $S_n$, and let $\mathrm{Li}^{-1}$ be the inverse of the offset logarithmic integral $\mathrm{Li}(x)=\int_2^x\frac{dt}{\ln t}$. If
--
--   $$
--   \ln g(n)<\sqrt{\mathrm{Li}^{-1}(n)}
--   $$
--
--   holds for all sufficiently large $n$, then the Riemann hypothesis is true.
--
--   This is one of the two directions of the Massias–Nicolas–Robin criterion, which states that the displayed inequality holds for all sufficiently large $n$ if and only if the Riemann hypothesis holds.
--
--   **Formalization Note** $g$ is `LandauFunction.landau` and $\mathrm{Li}^{-1}$ is `LandauFunction.logIntegralInv`, as in the full criterion `LandauFunction.landau_riemann_hypothesis_iff`.
-- source:
--   One direction of the criterion of J.-P. Massias, J.-L. Nicolas, G. Robin, "Évaluation asymptotique de l'ordre maximum d'un élément du groupe symétrique", Acta Arith. 50 (1988), 221–242; as quoted in Wikipedia, "Landau's function", revision oldid=1303222269 (https://en.wikipedia.org/w/index.php?title=Landau%27s_function&oldid=1303222269), sentence "The statement that ln g(n) < sqrt(Li^{-1}(n)) for all sufficiently large n is equivalent to the Riemann hypothesis".

import Mathlib
import Definitions.Def_LandauFunction_landau
import Definitions.Def_LandauFunction_logIntegral

namespace LandauFunction
theorem riemannHypothesis_of_landau
    (h : ∀ᶠ n : ℕ in Filter.atTop, Real.log (landau n) < Real.sqrt (logIntegralInv n)) :
    RiemannHypothesis := by sorry
end LandauFunction
