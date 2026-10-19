-- Prove2me | Theorems.Thm_ImperfReport_Regulator_prop_1_var_rk
-- name    : ImperfReport.Regulator.prop_1_var_rk
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:16.177441+00:00
-- url     : https://prove2.me/theorems/2cadd818-af36-4c13-8b4a-cfb7efac6867
-- title:
--   Proof of Proposition 1, p. 34: response and variance under (1, k)
-- statement:
--   Suppose $k>0$ and $k\le\alpha$, so the reporting system $(\hat\alpha_G,\hat\alpha_B)=(1,k)$ is feasible. Every information probability gives the firm its maximal threshold-crossing probability, so its tie-break selects $q=1$. The cutoff is zero and the regulator's remaining expected posterior variance is
--
--   $$\Psi(1,k)=k(1-\alpha).$$
--
--   This is the conservative comparison system used in Proposition 1. **Formalization Note** Feasibility $k\le\alpha$ is explicit here; the goal derives it from its corrected high-prior condition.
-- source:
--   Friedman, Hughes, Michaeli, A Rationale for Imperfect Reporting Standards, SSRN 3636995 (version of November 24, 2020), p. 34, Proof of Proposition 1, displayed variance

import Definitions.Def_ImperfReport_Regulator_Variance

set_option autoImplicit false
open MeasureTheory Set

namespace ImperfReport.Regulator

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020), p. 34, Proof of Proposition 1,
displayed variance at the reporting system `(1, k)`. Formalization Note:
`k ≤ α` makes this candidate feasible, while the strict high-prior condition
implies that inequality in the goal. The greatest-maximizer tie-break selects
`q = 1`; disclosure is for `s > t`, equivalent almost surely to `s ≥ t`. -/
theorem prop_1_var_rk (M : Model) (hM : M.Standing)
    (hk0 : 0 < M.k) (hka : M.k ≤ M.alpha) :
    (∀ q : ℝ, FirmBR M (rk M) q ↔ q = 1) ∧
    tdag M 1 = 0 ∧ Psi M (rk M) 1 = M.k * (1 - M.alpha) := by sorry

end ImperfReport.Regulator
