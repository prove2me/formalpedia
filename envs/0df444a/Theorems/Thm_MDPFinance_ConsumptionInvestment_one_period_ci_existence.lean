-- Prove2me | Theorems.Thm_MDPFinance_ConsumptionInvestment_one_period_ci_existence
-- name    : MDPFinance.ConsumptionInvestment.one_period_ci_existence
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T21:59:46.006396+00:00
-- url     : https://prove2.me/theorems/145605e8-420c-4f90-a3f0-ea4564d2964a
-- title:
--   Theorem 4.3.1 — one-period consumption-investment existence/regularity
-- statement:
--   Let $U_c$, $U_p$ be utility functions with $\mathrm{dom}\,U_c = \mathrm{dom}\,U_p =
--   [0,\infty)$. Then: a) there is no arbitrage iff there is a measurable $f^*: \mathrm{dom}\,U_p
--   \to \mathbb{R}_{\ge0}\times\mathbb{R}^d$ with $u(x,f^*(x))=v(x)$; b) $v$ is strictly increasing,
--   strictly concave and continuous.
--
--   **Formalization Note.** The consumption-investment analogue of chunk `04a`'s Theorem 4.1.1,
--   proved (per the book) "along the same lines," via the iterated supremum
--   $\sup_{(c,a)} u = \sup_c \sup_a u$ — not separately formalized here since it is a proof
--   technique, not part of the statement.
--
--   **Formalization Note (moderation).** $1+i>0$ added; $u$, $v$ are $[-\infty,\infty)$-valued and
--   $v$'s strict concavity is `StrictConcaveOnEReal`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 95, PDF 109, Theorem 4.3.1

import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_OnePeriod

open MeasureTheory ProbabilityTheory

namespace MDPFinance.ConsumptionInvestment

/-- Theorem 4.3.1 (Bäuerle–Rieder, p. 95, PDF 109). In the one-period market (bond factor
`1 + i > 0`, `𝔼‖R‖ < ∞`), let `Uc` and `Up` be utility functions with `domUc = domUp = [0,∞)`.
Then: a) there are no arbitrage opportunities iff there is a measurable
`f* : domUp → ℝ_{\ge0} × ℝ^d` with `u(x,f*(x)) = v(x)` for all `x ∈ domUp`; b) `v` is strictly
increasing, strictly concave and continuous on `domUp`. -/
theorem one_period_ci_existence {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (measIP : Measure Ω) [IsProbabilityMeasure measIP] (domUp : Set ℝ)
    (hdomUp : domUp = Set.Ici (0 : ℝ)) (Uc Up : ℝ → ℝ)
    (hUc : StrictMonoOn Uc domUp ∧ StrictConcaveOn ℝ domUp Uc ∧ ContinuousOn Uc domUp)
    (hUp : StrictMonoOn Up domUp ∧ StrictConcaveOn ℝ domUp Up ∧ ContinuousOn Up domUp)
    (i : ℝ) (hi : 0 < 1 + i) (R : Ω → Fin d → ℝ) (hR_meas : Measurable R)
    (hR_integrable : Integrable (fun ω => ∑ k, |R ω k|) measIP) :
    (NoArbitrageOnePeriodCI measIP R ↔
      ∃ fstar : ℝ → ℝ × (Fin d → ℝ), Measurable fstar ∧
        ∀ x ∈ domUp, OnePeriodCIU measIP Uc Up i R x (fstar x) =
          OnePeriodCIV measIP domUp Uc Up i R x) ∧
      StrictMonoOn (OnePeriodCIV measIP domUp Uc Up i R) domUp ∧
      StrictConcaveOnEReal domUp (OnePeriodCIV measIP domUp Uc Up i R) ∧
      ContinuousOn (OnePeriodCIV measIP domUp Uc Up i R) domUp := by sorry

end MDPFinance.ConsumptionInvestment
