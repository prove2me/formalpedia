-- Prove2me | Theorems.Thm_MDPFinance_MeanVariance_saddle_point_value
-- name    : MDPFinance.MeanVariance.saddle_point_value
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:07:09.589255+00:00
-- url     : https://prove2.me/theorems/28f9c3aa-f8a2-4a47-9a1f-d64d2ea288e0
-- title:
--   Lemma 4.6.2 — a saddle point of the Lagrangian solves (MV)
-- statement:
--   If $(\pi^*,\lambda^*)$ is a saddle point of the Lagrangian $L_{x_0}(\pi,\lambda)$ —
--   i.e. $\sup_{\lambda\ge0} L_{x_0}(\pi^*,\lambda) = L_{x_0}(\pi^*,\lambda^*) =
--   \inf_{\pi} L_{x_0}(\pi,\lambda^*)$ — then
--   $$\inf_\pi \sup_{\lambda\ge0} L_{x_0}(\pi,\lambda) = \sup_{\lambda\ge0}\inf_\pi
--   L_{x_0}(\pi,\lambda) = L_{x_0}(\pi^*,\lambda^*),$$
--   and $\pi^*$ is optimal for (MV).
--
--   This is the pivot of the whole chapter's technique: (MV) is not a standard Markov Decision
--   Problem because the variance is not additive across time, so no direct Bellman equation for
--   $\mathrm{Var}_{x_0}^\pi[X_N]$ exists. Rewriting the min-max value of (MV) as a Lagrangian
--   saddle point, and showing any saddle point gives the exact value and an optimal strategy, is what
--   lets the rest of the section reduce (MV) to the tractable auxiliary problems $P(\lambda)$ and
--   $QP(b)$.
--
--   **Formalization Note.** This is the exact result flagged as domain-mismatched with the platform's
--   `VectorSpaceOpt.lagrangian_saddle_sufficient_pointed` (over a closed convex cone in a normed
--   space) and `ConvexOptimization.lagrangian_saddle_iff_strong_duality`: here the primal domain is
--   the finite-horizon admissible-policy space $F^N$, not a Euclidean or normed vector space, and the
--   Lagrange multiplier ranges over $[0,\infty)\subset\mathbb{R}$ rather than a dual cone, so the
--   statement is restated locally rather than reused.
--
--   **Formalization Note (moderation).** The inner supremum over $\lambda\ge 0$ is $+\infty$ for
--   an infeasible $\pi$; the suprema and infima are therefore taken in $[-\infty,\infty]$ (a real
--   supremum would return $0$ on an unbounded set and could fall below the true value).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 119, PDF 133, Lemma 4.6.2

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- Lemma 4.6.2 (Bäuerle–Rieder, p. 119, PDF 133). Let `(π^*,λ^*)` be a saddle-point of
`L_{x_0}(π,λ)`. Then the value of `(MV)` is
`inf_{π∈F^N} sup_{λ≥0} L_{x_0}(π,λ) = sup_{λ≥0} inf_{π∈F^N} L_{x_0}(π,λ) = L_{x_0}(π^*,λ^*)`
(the inner suprema and infima taken in `[-∞,∞]`, an infeasible `π` having `sup_λ = +∞`), and `π^*`
is optimal for `(MV)`. -/
theorem saddle_point_value {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : MVMarket Ω d)
    (πstar : ℕ → ℝ → (Fin d → ℝ)) (lamstar : ℝ) (hsaddle : M.IsSaddlePoint πstar lamstar) :
    (⨅ π ∈ {π | M.IsAdmissible 0 π}, ⨆ lam ∈ Set.Ici (0 : ℝ), (M.Lagrangian π lam : EReal)) =
        (⨆ lam ∈ Set.Ici (0 : ℝ), ⨅ π ∈ {π | M.IsAdmissible 0 π}, (M.Lagrangian π lam : EReal)) ∧
      (⨆ lam ∈ Set.Ici (0 : ℝ), ⨅ π ∈ {π | M.IsAdmissible 0 π}, (M.Lagrangian π lam : EReal)) =
        (M.Lagrangian πstar lamstar : EReal) ∧
      M.IsOptimalMV πstar := by sorry

end MDPFinance.MeanVariance
