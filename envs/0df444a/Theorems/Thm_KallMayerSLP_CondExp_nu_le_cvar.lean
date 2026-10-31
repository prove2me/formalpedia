-- Prove2me | Theorems.Thm_KallMayerSLP_CondExp_nu_le_cvar
-- name    : KallMayerSLP.CondExp.nu_le_cvar
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:11:52.517201+00:00
-- url     : https://prove2.me/theorems/a853a270-c2e5-4e30-a012-c33caa3c0160
-- title:
--   §4.3, p.162 — $\nu_c(\vartheta,\alpha)\ge\nu(\vartheta,\alpha)$
-- statement:
--   Let $\vartheta$ have finite expected value and $0<\alpha<1$. Then the value at risk $\nu(\vartheta,\alpha)$ is an optimal solution of (4.30), so the minimum defining $\nu_c(\vartheta,\alpha)$ is attained there, and
--   $$
--   \nu_c(\vartheta,\alpha)\ge\nu(\vartheta,\alpha).
--   $$
--
--   CVaR is thus a conservative bound on VaR.
--
--   Differences from the source:
--   - encoding: min_z in (4.32) → sInf of the range, with attainment at ν(ϑ, α) as a clause of the theorem; reason: attainment is the book's own statement that the value at risk is an optimal solution
--   - encoding: ν(ϑ, α) an optimal solution of (4.29) → ν(ϑ, α) a minimizer of the objective of (4.30); reason: p.160 shows the objective of (4.29) is (1 − α) times that of (4.30) minus a constant, so both have the same minimizers
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §4.3, pp.161–162

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_KallMayerSLP_CondExp_cvarObjective
import Definitions.Def_KallMayerSLP_CondExp_cvar

open MeasureTheory

namespace KallMayerSLP.CondExp

/-- The value-at-risk `ν(ϑ, α)` is an optimal solution of (4.30), so the `min` in (4.32) is attained
there, and substituting it gives `ν_c(ϑ, α) ≥ ν(ϑ, α)`.
Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §4.3, pp.161–162 (PDF 171–172). -/
theorem nu_le_cvar {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ϑ : Ω → ℝ) (hϑ : Measurable ϑ) (hint : Integrable ϑ μ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    IsMinOn (cvarObjective μ ϑ α) Set.univ (MultistageStochastic.valueAtRisk μ ϑ α) ∧
      cvar μ ϑ α = cvarObjective μ ϑ α (MultistageStochastic.valueAtRisk μ ϑ α) ∧
      MultistageStochastic.valueAtRisk μ ϑ α ≤ cvar μ ϑ α := by sorry

end KallMayerSLP.CondExp
