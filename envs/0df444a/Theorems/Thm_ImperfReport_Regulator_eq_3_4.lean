-- Prove2me | Theorems.Thm_ImperfReport_Regulator_eq_3_4
-- name    : ImperfReport.Regulator.eq_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:14.601503+00:00
-- url     : https://prove2.me/theorems/f0a1a662-97b0-4151-897d-b46436850a00
-- title:
--   Proof of Proposition 1, pp. 34–35: equations (3)–(4) as expected variance
-- statement:
--   Under the perfectly informative reporting system and $0<k<\beta$, let $q_0=q^\dagger(k)$ and $P=1-q_0(1-F(k))$, the probability of nondisclosure. Multiplying the conditional variance in the paper's equation (3) by $P$ gives the regulator's expected posterior variance. It simplifies to
--
--   $$\Psi(1,0;q_0)=m_2-q_0\int_{(k,1]}x^2\,d\mu(x)-k^2P.$$
--
--   The statement also records the weighted version of the two conditional-mixture terms in (3). This identity supplies the corrected comparison in Proposition 1. **Formalization Note** Equation (3) itself is conditional on nondisclosure despite its expected-variance label; $P$ is therefore essential.
-- source:
--   Friedman, Hughes, Michaeli, A Rationale for Imperfect Reporting Standards, SSRN 3636995 (version of November 24, 2020), pp. 34–35, Proof of Proposition 1, equations (3)–(4), corrected expected-variance weighting

import Definitions.Def_ImperfReport_Regulator_Variance

set_option autoImplicit false
open MeasureTheory Set

namespace ImperfReport.Regulator

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020), pp. 34–35, Proof of Proposition 1,
equations (3)–(4), weighted by the nondisclosure probability. The paper's (3)
uses conditional weights; `Psi` is the expected posterior variance, so the
first identity multiplies (3) by `P = Pr(m = ∅)`. The second is the simplified
form used in the corrected threshold. `F(k) > 0` follows from full support. -/
theorem eq_3_4 (M : Model) (hM : M.Standing)
    (hk0 : 0 < M.k) (hkb : M.k < beta M) :
    let q₀ := qdag M M.k
    let P := 1 - q₀ * (1 - F M M.k)
    Psi M perfect q₀ =
      P * ((1 - q₀) / P * (m2 M - M.k ^ 2) +
        q₀ * F M M.k / P *
          ((∫ x in Set.Iic M.k, x ^ 2 ∂M.mu) / F M M.k - M.k ^ 2)) ∧
    Psi M perfect q₀ =
      m2 M - q₀ * (∫ x in Set.Ioc M.k 1, x ^ 2 ∂M.mu) - M.k ^ 2 * P := by sorry

end ImperfReport.Regulator
