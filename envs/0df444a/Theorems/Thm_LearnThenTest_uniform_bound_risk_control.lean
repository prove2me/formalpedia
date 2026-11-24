-- Prove2me | Theorems.Thm_LearnThenTest_uniform_bound_risk_control
-- name    : LearnThenTest.uniform_bound_risk_control
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T00:13:08.949051+00:00
-- url     : https://prove2.me/theorems/c1c96532-fdf9-4033-a2c7-4b6db29279ee
-- title:
--   Proposition 7: uniform bounds give risk control
-- statement:
--   Let $\Lambda$ be any parameter set with risks $R(\lambda)$. Let $R^+$ be a $1-\delta$ uniform upper confidence bound: a random function on $\Lambda$ with
--
--   $$\mathbb P\big(R(\lambda)\le R^+(\lambda)\text{ for all }\lambda\in\Lambda\big)\ge1-\delta.$$
--
--   Let $\alpha\in\mathbb R$, and let $\hat\lambda$ be any random parameter with $R^+(\hat\lambda)\le\alpha$. Then $\mathcal T_{\hat\lambda}$ is an $(\alpha,\delta)$-risk-controlling prediction: $\mathbb P\big(R(\hat\lambda)\le\alpha\big)\ge1-\delta$.
--
--   This is the alternative to multiple testing studied in Appendix F of the paper.
--
--   **Formalization Note** The condition $R^+(\hat\lambda)\le\alpha$ is required on every outcome. The paper's proof says "fails with probability at most $\alpha$", which is a typo for $\delta$.
-- source:
--   Angelopoulos, Bates, Candès, Jordan and Lei, Learn then Test: Calibrating Predictive Algorithms to Achieve Risk Control, arXiv:2110.01052v5 (2022), Section 2.5, Proposition 7, p. 7; proof in Appendix C, p. 22

import Mathlib
import Definitions.Def_LearnThenTest_Basic

open MeasureTheory ProbabilityTheory Filter

namespace LearnThenTest

theorem uniform_bound_risk_control {Ω L : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (R : L → ℝ) (Rplus : Ω → L → ℝ) (α δ : ℝ)
    (hRplus : ENNReal.ofReal (1 - δ) ≤ P {ω | ∀ l, R l ≤ Rplus ω l})
    (lhat : Ω → L) (hlhat : ∀ ω, Rplus ω (lhat ω) ≤ α) :
    IsRCP P R α δ lhat := by sorry

end LearnThenTest
