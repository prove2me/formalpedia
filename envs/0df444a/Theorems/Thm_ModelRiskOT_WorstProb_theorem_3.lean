-- Prove2me | Theorems.Thm_ModelRiskOT_WorstProb_theorem_3
-- name    : ModelRiskOT.WorstProb.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:05:39.438604+00:00
-- url     : https://prove2.me/theorems/547ac8a7-40a9-457f-b43b-9f65366b06f5
-- title:
--   Theorem 3 — $\sup\{P(A) : d_c(\mu,P) \le \delta\} = \mu\{x : c(x,A) \le 1/\lambda^*\}$ when $\underline c = \overline c$
-- statement:
--   Let $S$ be a Polish space, $c : S \times S \to \mathbb R_+$ a cost satisfying (A1) (nonnegative, lower semicontinuous, $c(x,y) = 0 \iff x = y$), $\mu$ a probability measure on $S$, $\delta > 0$, and $A \subseteq S$ a nonempty closed set. Write $c(x,A) = \inf_{y\in A} c(x,y)$. Suppose that $\lambda^* \in [0,\infty)$ attains the infimum in
--   $$\inf_{\lambda \ge 0}\Big\{\lambda\delta + E_\mu\big[(1 - \lambda c(X,A))^+\big]\Big\} \tag{13}$$
--   and that the quantities $\underline c := \int_{\{c(x,A) < 1/\lambda^*\}} c(x,A)\,d\mu(x)$ and $\overline c := \int_{\{c(x,A) \le 1/\lambda^*\}} c(x,A)\,d\mu(x)$ of (14) are equal. Then
--   $$\sup\{P(A) : d_c(\mu,P) \le \delta\} = \mu\{x : c(x,A) \le 1/\lambda^*\}. \tag{15}$$
--
--   The worst-case probability of $A$ over all models within optimal transport cost $\delta$ of the baseline is the baseline probability of the inflated set $\{x : c(x,A) \le 1/\lambda^*\}$. No optimal transport plan is assumed to exist.
--
--   **Formalization Note** The threshold $c(x,A) \le 1/\lambda^*$ is written $\lambda^* c(x,A) \le 1$, which is the whole space at $\lambda^* = 0$ (the paper's $1/0 = \infty$; then both sides equal $1$). The supremum is over probability measures $P$ on $S$ with $d_c(\mu,P) \le \delta$, with both marginals of the couplings in $d_c$ fixed. Both sides are in $[0,\infty]$; $\mu$ of the inflated set, which is universally measurable, is its outer measure, i.e. its completion measure.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 10, Theorem 3, Eq. (15)

import Mathlib
import Definitions.Def_ModelRiskOT_WorstProb_WorstCaseProb

open MeasureTheory
open scoped ENNReal

namespace ModelRiskOT.WorstProb

/-- Theorem 3, p. 10, (15). Under (A1), for a nonempty closed `A`, if `λ* ∈ [0, ∞)` attains the
infimum in (13) and `c̲ = c̄` (14), then
`sup {P(A) : d_c(μ, P) ≤ δ} = μ {x : c(x, A) ≤ 1/λ*}`.
The threshold is in multiplied form `λ* c(x, A) ≤ 1` (the whole space at `λ* = 0`, i.e. `1/0 = ∞`).

Sanity check (not part of the statement): `S = ℝ`, `c(x, y) = |x − y|`, `μ` uniform on `[0, 1]`,
`A = [1, ∞)`, `0 < δ ≤ 1/2`. Then `c(x, A) = 1 − x` on `[0, 1]`, `g(λ) = λδ + 1/(2λ)` for `λ ≥ 1`,
minimized at `λ* = 1/√(2δ)` with value `√(2δ)`, `c̲ = c̄ = δ`, and
`μ {x : 1 − x ≤ √(2δ)} = √(2δ)`: both sides agree and are strictly between 0 and 1.
With `μ` the point mass at `0` and `δ < 1`, instead, `λ* = 1`, `c̲ = 0 ≠ 1 = c̄`: the hypothesis
fails, and indeed `I = δ ≠ 1`. -/
theorem theorem_3 {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S] (c : S → S → ℝ) (hc : ModelRiskOT.Duality.AssumptionA1 c) (μ : Measure S) [IsProbabilityMeasure μ]
    (δ : ℝ) (hδ : 0 < δ) (A : Set S) (hA : IsClosed A) (hAne : A.Nonempty)
    (lamStar : ℝ) (hlam : AttainsInf13 c μ δ A lamStar)
    (hcc : cLower c μ A lamStar = cUpper c μ A lamStar) :
    worstProb c μ δ A = μ {x | lamStar * costToSet c A x ≤ 1} := by sorry

end ModelRiskOT.WorstProb
