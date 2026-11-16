-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_Supplement_budget_constrained_extraction
-- name    : IndependentInfoPricing.Main.Supplement.budget_constrained_extraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:55:42.131198+00:00
-- url     : https://prove2.me/theorems/18b3e77b-9b96-4ebd-b65d-92529c8d51da
-- title:
--   Lemma 4.15 — Budget-constrained extraction
-- statement:
--   In a fixed orthant (54) with $m,n\ge1$ whose magnitudes $X_1,\dots,X_m,Y_1,\dots,Y_n$ are independent and regular (scope of §4.4), let $\bar a=\sum_i\operatorname{Rev}(X_i)$ and $\bar b=\sum_j\operatorname{Rev}(Y_j)$ as in (56), and let $\operatorname{Sep}_\pm$ be the budget-constrained separate-selling revenues (64). Then for every $t\ge0$,
--   $$\operatorname{Sep}_+(t)\ge\frac12\min\{\bar a,t\},\qquad\operatorname{Sep}_-(t)\ge\frac12\min\{\bar b,t\}.\tag{65}$$
--
--   Budget-constrained separate selling is the device by which the smaller side's classical revenue is transferred to the information problem in Lemma 4.18.
--
--   **Formalization Note** The positive block is a set $S$ of coordinates (instead of re-indexing so that it comes first); $\bar a,\bar b$ are the base `aBar`, `bBar`.
--
--   Differences from the source:
--   - reading: a continuously differentiable density, positive throughout an interval support, with pointwise values at a finite left endpoint understood as right limits (possibly extended) → a density version f : ℝ → [0,∞] that is finite, positive and C¹ on the interior of the topological support, the support being an interval; the hazard η at the left endpoint is the liminf of t·f(t)/S(t) from the interior; reason: endpoint values are one-sided limits in the source, so positivity is imposed where the density is evaluated pointwise (the interior); the liminf equals the source's one-sided limit whenever that limit exists, which regularity guarantees
--   - encoding: regularity: ψ_D(t) = t − 1/h_D(t) nondecreasing on the support → ψ_D(t) = t − S_D(t)/f(t) monotone on the interior of the support; reason: the endpoint values of ψ_D are one-sided limits of interior values, so monotonicity on the interior is monotonicity on the support
--   - encoding: after re-indexing, v = (X_1,…,X_m,−Y_1,…,−Y_n) → a coordinate set S with v_i > 0 a.s. on S and v_j < 0 a.s. off S, both nonempty; reason: the same fixed orthant without re-indexing
--   - encoding: real expected revenues, suprema and probabilities → nonnegative extended reals (ℝ≥0∞): lintegrals, suprema and measures; reason: the base mission's convention; it represents every finite value unchanged and avoids default-zero integrals
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Lemma 4.15, printed p.40 (PDF p.42); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Supplement_Orthant

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main.Supplement

open IndependentInfoPricing.Main

/-- Lemma 4.15, p.40 (PDF 42), (65): budget-constrained extraction in a regular fixed orthant. -/
theorem budget_constrained_extraction {Q : ℕ} (F : Marginals (Fin Q)) (S : Finset (Fin Q))
    (hF : RegularOrthant F S) (t : ℝ) (ht : 0 ≤ t) :
    (1 / 2 : ℝ≥0∞) * min (aBar F S) (ENNReal.ofReal t) ≤ sepPlus F S t ∧
    (1 / 2 : ℝ≥0∞) * min (bBar F S) (ENNReal.ofReal t) ≤ sepMinus F S t := by sorry


end IndependentInfoPricing.Main.Supplement
