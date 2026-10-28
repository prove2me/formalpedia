-- Prove2me | Theorems.Thm_ImperfReport_Regulator_proposition_1
-- name    : ImperfReport.Regulator.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:03.630723+00:00
-- url     : https://prove2.me/theorems/22467b5f-d4ee-4f76-9e15-707e4fa7e0f2
-- title:
--   Proposition 1: a conservative report beats a perfect report under a corrected high-prior threshold
-- statement:
--   Consider a model with $0<k<\beta$ and a high prior $\alpha>\alpha^\circ$, where the corrected threshold is
--
--   $$\alpha^\circ=1+k\bigl(1-q^\dagger(k)(1-F(k))\bigr)-\frac{m_2-q^\dagger(k)\int_{(k,1]}x^2\,d\mu(x)}{k}.$$
--
--   Then the conservative system $(1,k)$ is feasible. Both it and the perfectly informative system $(1,0)$ have a firm best response, and the regulator's expected posterior variance under $(1,k)$ is strictly lower than under $(1,0)$. Consequently, every regulator optimum whose good-report posterior is one has a strictly positive bad-report posterior.
--
--   This is the imperfect-reporting conclusion of Proposition 1 under the corrected threshold. **Formalization Note** The source's printed $\alpha^\circ$ compares conditional and expected variances. For uniform $\omega_2$, $k=0.15$ and $\alpha=0.8333$ satisfy its printed bound $0.7167$, yet $(1,0)$ has lower variance than $(1,k)$; the corrected bound is $0.95$. The first sentence of the proposition, which asserts that all optima have good posterior one, is outside this goal.
-- source:
--   Friedman, Hughes, Michaeli, A Rationale for Imperfect Reporting Standards, SSRN 3636995 (version of November 24, 2020), p. 18, Proposition 1, second sentence; pp. 34–35, proof and corrected equation (5)

import Definitions.Def_ImperfReport_Regulator_Variance

set_option autoImplicit false
open MeasureTheory Set

namespace ImperfReport.Regulator

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020), p. 18, Proposition 1, second
sentence, and pp. 34–35, proof, with the corrected sufficient threshold.
Formalization Note: the printed `α° = 1 + k − V/(k P)` is false because (3)
is conditional on nondisclosure whereas the regulator minimizes an expected
variance. The correction is `α° = 1 + k P − V/k`, encoded by `alphaO`.
For uniform `ω₂`, `k = 0.15` and `α = 0.8333` satisfy the printed threshold
`0.7167` yet `(1, 0)` has lower variance than `(1, k)`; the corrected threshold
is `1 − k/3 = 0.95`. The first sentence of Proposition 1 is outside this goal,
so the optimality clause quantifies over optima whose good posterior is `1`.
The best-response existence and strict comparison prevent a vacuous conclusion. -/
theorem proposition_1 (M : Model) (hM : M.Standing)
    (hk0 : 0 < M.k) (hkb : M.k < beta M) (hα : alphaO M < M.alpha) :
    (rk M).Valid M ∧
    (∃ q, FirmBR M perfect q) ∧
    (∃ q, FirmBR M (rk M) q) ∧
    (∀ q q', FirmBR M perfect q → FirmBR M (rk M) q' →
      Psi M (rk M) q' < Psi M perfect q) ∧
    (∀ (r : Report) (q : ℝ), RegOpt M r q → r.aG = 1 → 0 < r.aB) := by sorry

end ImperfReport.Regulator
