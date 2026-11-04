-- Prove2me | Theorems.Thm_ImpactCopula_proposition_A9
-- name    : ImpactCopula.proposition_A9
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:55:45.532596+00:00
-- url     : https://prove2.me/theorems/8b04c585-54a2-457f-8648-4a167498aa8a
-- title:
--   Proposition A.9 — a linearly interpolating copula exists and is unique on $[0,1]\times\overline{\mathcal R}_\theta$
-- statement:
--   Let $F$ be any bivariate distribution, with law $\mu$ on $\mathbb R^2$. Then:
--
--   1. there exists a copula $C$ of $F$ that is linearly interpolating on $\overline{\mathcal R}_X^c \times \overline{\mathcal R}_\theta$ with respect to $u$, i.e. satisfies (13);
--   2. any two such copulas $C, C'$ agree on $[0,1] \times \overline{\mathcal R}_\theta$:
--
--   $$
--   C(u, v) = C'(u, v), \qquad u \in [0,1],\ v \in \overline{\mathcal R}_\theta .
--   $$
--
--   So the condition of Theorem 2 can always be met, and it pins the copula down wherever the representation can see it.
--
--   Differences from the source:
--   - encoding: bivariate distribution $F$; copulas on $[0,1]^2$ → probability measure $\mu$ on $\mathbb R^2$; functions `ℝ → ℝ → ℝ` satisfying `coIsCopula`, uniqueness stated pointwise on $[0,1] \times \overline{\mathcal R}_\theta$; reason: Lean convention; same statement.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), Appendix A.3.1, Proposition A.9, p.43 (PDF p.46); proof in Appendix C.8, p.95 (PDF p.98)

import Mathlib
import Definitions.Def_ImpactCopula_IsCopulaOf
import Definitions.Def_ImpactCopula_IsLinearlyInterpolating

open MeasureTheory

namespace ImpactCopula

/-- **Proposition A.9**, Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024), p.43 (PDF p.46): "For any bivariate distribution F, there exists a
copula of F that satisfies (13) on R̄_X^c × R̄_θ. In addition, the copula is unique on
[0, 1] × R̄_θ."

**Formalization Note.** `F` is an arbitrary probability measure `μ` on `ℝ²`. Copulas are
functions on `ℝ²` constrained on `[0, 1]²`, so uniqueness is stated on `[0, 1] × R̄_θ`: any two
linearly interpolating copulas of `μ` agree there. -/
theorem proposition_A9 (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] :
    (∃ C : ℝ → ℝ → ℝ, IsCopulaOf C μ ∧ IsLinearlyInterpolating C μ) ∧
      ∀ C C' : ℝ → ℝ → ℝ, IsCopulaOf C μ → IsLinearlyInterpolating C μ →
        IsCopulaOf C' μ → IsLinearlyInterpolating C' μ →
          ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ rbarTheta μ, C u v = C' u v := by sorry

end ImpactCopula
