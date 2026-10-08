-- Prove2me | Theorems.Thm_ModelRiskOT_WorstProb_eq_13
-- name    : ModelRiskOT.WorstProb.eq_13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:05:06.455394+00:00
-- url     : https://prove2.me/theorems/d8888aa4-efaf-46f4-900e-c3a160cadec6
-- title:
--   (13) — $\sup\{P(A) : d_c(\mu,P) \le \delta\} = \inf_{\lambda \ge 0}\{\lambda\delta + E_\mu[(1 - \lambda c(X,A))^+]\}$
-- statement:
--   Let $S$ be a Polish space, $c$ a cost satisfying (A1), $\mu$ a probability measure on $S$, $\delta > 0$, and $A \subseteq S$ a nonempty closed set. Then the worst-case probability (12) is the value of a univariate convex problem:
--   $$\sup\{P(A) : d_c(\mu,P) \le \delta\} = \inf_{\lambda \ge 0}\Big\{\lambda\delta + E_\mu\big[(1 - \lambda c(X,A))^+\big]\Big\}.$$
--
--   The only measure on the right-hand side is the baseline $\mu$, so the infinite-dimensional worst case is computed by a one-dimensional minimization. It is the specialization of the paper's strong duality theorem (Theorem 1, with Remark 1's (9)) to $f = 1_A$, which is upper semicontinuous because $A$ is closed.
--
--   **Formalization Note** Both sides are in $[0,\infty]$; the expectation is a lower Lebesgue integral, which equals the integral under the completion of $\mu$ since $x \mapsto c(x,A)$ is universally measurable.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 9, Eq. (13)

import Mathlib
import Definitions.Def_ModelRiskOT_WorstProb_WorstCaseProb

open MeasureTheory
open scoped ENNReal

namespace ModelRiskOT.WorstProb

/-- (13), p. 9: for a nonempty closed set `A`, the worst-case probability (12) is the value of a
univariate problem,
`sup {P(A) : d_c(μ, P) ≤ δ} = inf_{λ ≥ 0} {λδ + E_μ[(1 − λ c(X, A))⁺]}`. -/
theorem eq_13 {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S] (c : S → S → ℝ) (hc : ModelRiskOT.Duality.AssumptionA1 c) (μ : Measure S) [IsProbabilityMeasure μ]
    (δ : ℝ) (hδ : 0 < δ) (A : Set S) (hA : IsClosed A) (hAne : A.Nonempty) :
    worstProb c μ δ A = ⨅ lam ∈ Set.Ici (0 : ℝ), obj13 c μ δ A lam := by sorry

end ModelRiskOT.WorstProb
