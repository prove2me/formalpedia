-- Prove2me | Theorems.Thm_ImpactCopula_eq_A73
-- name    : ImpactCopula.eq_A73
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:57:20.826831+00:00
-- url     : https://prove2.me/theorems/611c1418-c37f-4b9c-945d-08a37851dde3
-- title:
--   Eq. (A.73) — $\tilde g(F_X(F_X^{-1}(u)), w) = g(u,w)$ off a null set
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R^2$ and $C$ a copula of $\mu$ that is linearly interpolating on $\overline{\mathcal R}_X^c \times \overline{\mathcal R}_\theta$ with respect to $u$. Let $g(u,w) = F_\theta^{-1}(g_u(w))$ be the mixture function (15) and $\tilde g(u,w) = F_\theta^{-1}(\tilde g_u(w))$ its modification (A.71). Then there is a Lebesgue-null set $E_2$ such that
--
--   $$
--   \tilde g\big(F_X(F_X^{-1}(u)), w\big) = g(u, w), \qquad u \in [0,1]\setminus E_2,\ w \in [0,1] . \tag{A.73}
--   $$
--
--   Differences from the source:
--   - encoding: inverses $F_X^{-1}$, $g_u$, $\tilde g_u$, $F_\theta^{-1}$ with values $\pm\infty$ → real-valued `sInf`s (junk value $0$); reason: at $u \in \{0,1\}$ the difference is absorbed by $E_2$; for $u \notin E_2$ and every $w \in [0,1]$, endpoints included, both sides are the `EReal.toReal` of the paper's values ($0$ for both at $w = 0$), so the equality is the paper's.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), Appendix C.3, proof of Theorem 2, step three, eq. (A.73), p.80 (PDF p.83)

import Mathlib
import Definitions.Def_ImpactCopula_IsCopulaOf
import Definitions.Def_ImpactCopula_IsLinearlyInterpolating
import Definitions.Def_ImpactCopula_mixture
import Definitions.Def_ImpactCopula_mixtureTilde

open MeasureTheory

namespace ImpactCopula

/-- **(A.73)**, proof of Theorem 2, step three, Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024), p.80 (PDF p.83): for a linearly
interpolating copula `C` of `F` there is a Lebesgue-null set `E₂` with
`g̃(F_X(F_X⁻¹(u)), w) = g(u, w)` for `u ∈ [0, 1] \ E₂` and `w ∈ [0, 1]`.

**Formalization Note.** `g` is the mixture function (15) (`mixture`), `g̃` is (A.71)
(`mixtureTilde`), `F_X⁻¹` the published `quantileFunction` of `μ.map Prod.fst`. All inverses are
real-valued; the endpoints `w = 0` and `w = 1` are included, as printed, and the statement is
true there in this convention (both sides are `0` at `w = 0`; at `w = 1` the real values are the
`EReal.toReal` of the paper's). -/
theorem eq_A73 (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] (C : ℝ → ℝ → ℝ)
    (hC : IsCopulaOf C μ) (hLI : IsLinearlyInterpolating C μ) :
    ∃ E₂ : Set ℝ, volume E₂ = 0 ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1, u ∉ E₂ → ∀ w ∈ Set.Icc (0 : ℝ) 1,
        mixtureTilde C μ
            (cdfX μ (RiskFunctionals.StochDominance.quantileFunction (μ.map Prod.fst) u)) w =
          mixture C μ u w := by sorry

end ImpactCopula
