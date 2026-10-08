-- Prove2me | Theorems.Thm_ModelRiskOT_WorstProb_lemma_2
-- name    : ModelRiskOT.WorstProb.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:05:27.566162+00:00
-- url     : https://prove2.me/theorems/69a319cc-02aa-4630-9209-6480222c2102
-- title:
--   Lemma 2 — $\underline c \le \delta \le \overline c$ if $\lambda^* > 0$; $\delta \ge \overline c = \underline c$ if $\lambda^* = 0$
-- statement:
--   Let $S$ be a Polish space, $c$ a cost satisfying (A1), $\mu$ a probability measure on $S$, $\delta > 0$, and $A \subseteq S$ a nonempty closed set. Let $\underline c$ and $\overline c$ be the quantities (14) defined in terms of $\lambda^*$.
--   1. If $\lambda^* \in (0,\infty)$ attains the infimum in (13), then $$\underline c \le \delta \le \overline c.$$
--   2. If the infimum in (13) is attained at $\lambda^* = 0$, then $$\delta \ge \overline c = \underline c.$$
--
--   The lemma locates the budget $\delta$ between the transport costs of the two extreme ways of moving mass into $A$ at level $1/\lambda^*$: moving all points with $c(x,A) < 1/\lambda^*$, or all points with $c(x,A) \le 1/\lambda^*$. It is the reason why, when $\underline c = \overline c$, the worst case is attained by moving exactly the inflated set $\{c(x,A) \le 1/\lambda^*\}$.
--
--   **Formalization Note** With the multiplied-form thresholds, at $\lambda^* = 0$ both sets in (14) are $S$, so $\underline c = \overline c = \int c(x,A)\,d\mu(x)$, as in the paper's proof. Values are in $[0,\infty]$ and $\delta$ enters as a nonnegative extended real.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 10, Lemma 2

import Mathlib
import Definitions.Def_ModelRiskOT_WorstProb_WorstCaseProb

open MeasureTheory
open scoped ENNReal

namespace ModelRiskOT.WorstProb

/-- Lemma 2, p. 10. Under (A1), for a nonempty closed `A`: if `λ* ∈ (0, ∞)` attains the infimum in
(13), then `c̲ ≤ δ ≤ c̄`; if the infimum in (13) is attained at `λ* = 0`, then `δ ≥ c̄ = c̲`
(`c̲`, `c̄` as in (14)). -/
theorem lemma_2 {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S] (c : S → S → ℝ) (hc : ModelRiskOT.Duality.AssumptionA1 c) (μ : Measure S) [IsProbabilityMeasure μ]
    (δ : ℝ) (hδ : 0 < δ) (A : Set S) (hA : IsClosed A) (hAne : A.Nonempty)
    (lamStar : ℝ) (hlam : AttainsInf13 c μ δ A lamStar) :
    (0 < lamStar →
      cLower c μ A lamStar ≤ ENNReal.ofReal δ ∧ ENNReal.ofReal δ ≤ cUpper c μ A lamStar) ∧
    (lamStar = 0 →
      cUpper c μ A lamStar ≤ ENNReal.ofReal δ ∧ cUpper c μ A lamStar = cLower c μ A lamStar) := by sorry

end ModelRiskOT.WorstProb
