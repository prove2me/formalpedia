-- Prove2me | Theorems.Thm_ImpactCopula_eq_A70
-- name    : ImpactCopula.eq_A70
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:55:50.120011+00:00
-- url     : https://prove2.me/theorems/68992b2c-5c02-42d1-9c90-c66d21bec7e5
-- title:
--   Eq. (A.70) — $\tilde D_1C(F_X(F_X^{-1}(u)), v) = D_1C(u,v)$ off a null set
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R^2$ and $C$ a copula of $\mu$ that is linearly interpolating on $\overline{\mathcal R}_X^c \times \overline{\mathcal R}_\theta$ with respect to $u$. Let $\tilde D_1C$ be the modified MPDD (A.67) and $F_X^{-1}(u) = \inf\{x : F_X(x) \ge u\}$. Then there is a Lebesgue-null set $E_2$ such that
--
--   $$
--   \tilde D_1C\big(F_X(F_X^{-1}(u)), v\big) = D_1C(u, v), \qquad u \in [0,1] \setminus E_2,\ v \in \overline{\mathcal R}_\theta . \tag{A.70}
--   $$
--
--   The map $u \mapsto F_X(F_X^{-1}(u))$ sends each gap $(F_X(d-), F_X(d))$ to its right end $F_X(d)$; (A.70) says this collapse does not change the conditional distribution function on $\overline{\mathcal R}_\theta$.
--
--   Differences from the source:
--   - encoding: $F_X^{-1}$ with values $\pm\infty$ at $u = 0$ (and $u = 1$ when $F_X < 1$) → the published real-valued `quantileFunction` of `μ.map Prod.fst`; reason: the two differ only at $u \in \{0, 1\}$, a null set absorbed by the existential $E_2$, as the paper's $E_2$ absorbs the points $F_X(d)$, $F_X(d-)$.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), Appendix C.3, proof of Theorem 2, step two, eq. (A.70), p.80 (PDF p.83)

import Mathlib
import Definitions.Def_ImpactCopula_IsCopulaOf
import Definitions.Def_ImpactCopula_IsLinearlyInterpolating
import Definitions.Def_ImpactCopula_mpddTilde
import Definitions.Def_ImpactCopula_rbarTheta
import Definitions.Def_RiskFunctionals_StochDominance_QuantileFunction

open MeasureTheory

namespace ImpactCopula

/-- **(A.70)**, proof of Theorem 2, step two, Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024), p.80 (PDF p.83): for a linearly interpolating
copula `C` of `F` there is a Lebesgue-null set `E₂` with
`D̃₁C(F_X(F_X⁻¹(u)), v) = D₁C(u, v)` for `u ∈ [0, 1] \ E₂`, `v ∈ R̄_θ`.

**Formalization Note.** `F_X⁻¹` is the published `quantileFunction` of `μ.map Prod.fst`
(Definition A.1, real-valued; its junk values at `u = 0` and, when `F_X < 1`, at `u = 1` are on
a null set, which the existential `E₂` absorbs, as the paper's `E₂` absorbs `F_X(d)`, `F_X(d−)`).
`D̃₁C` is (A.67), `mpddTilde`. -/
theorem eq_A70 (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] (C : ℝ → ℝ → ℝ)
    (hC : IsCopulaOf C μ) (hLI : IsLinearlyInterpolating C μ) :
    ∃ E₂ : Set ℝ, volume E₂ = 0 ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1, u ∉ E₂ → ∀ v ∈ rbarTheta μ,
        mpddTilde C μ (cdfX μ (RiskFunctionals.StochDominance.quantileFunction (μ.map Prod.fst) u)) v =
          mpdd C u v := by sorry

end ImpactCopula
