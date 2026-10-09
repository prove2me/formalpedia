-- Prove2me | Theorems.Thm_MultiItemRev_KBundling_theorem_D
-- name    : MultiItemRev.KBundling.theorem_D
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:11:44.079887+00:00
-- url     : https://prove2.me/theorems/63e8e691-fae2-4589-a5dc-9fe689bb8ee8
-- title:
--   Theorem D, p. 7 — ∃ c > 0, ∀ k ≥ 2, k i.i.d. goods: BRev ≥ (c/log k)·Rev
-- statement:
--   **Theorem D.** There exists a constant $c>0$ such that for any $k\ge2$ and any $k$ independent and identically distributed goods $X_1,\dots,X_k$, selling them as one bundle at the bundle-optimal price guarantees at least $c/\log k$ of the optimal revenue:
--   $$\mathrm{BRev}(X_1,\dots,X_k)\ge\frac{c}{\log k}\,\mathrm{Rev}(X_1,\dots,X_k).$$
--
--   For identically distributed goods, the simplest mechanism, a single posted price for the grand bundle, loses at most a logarithmic factor against the optimal mechanism, uniformly over the distribution. For independent but non-identical goods no such bound holds (bundling can get only a $1/k$ fraction, Example 27).
--
--   **Formalization Note** The constant $c$ is quantified before $k$ and the law $\nu$, so it is absolute. The paper states the result as $\mathrm{GFOR}(\textsc{bundled};k\text{ i.i.d. goods})\ge c/\log k$, an infimum of ratios $\mathrm{BRev}/\mathrm{Rev}$; the formal statement is the equivalent multiplicative inequality, which also covers $\mathrm{Rev}=\infty$ (then $\mathrm{BRev}=\infty$ is required) without the ratio convention. $\log$ is the natural logarithm (the base only rescales $c$).
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 7, Theorem D (proof pp. 26–27)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.KBundling

theorem theorem_D :
    ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ), 2 ≤ k →
      ∀ (ν : Measure ℝ≥0) [IsProbabilityMeasure ν],
        ENNReal.ofReal (c / Real.log (k : ℝ)) *
            MultiItemRev.Decomp.Rev (Measure.pi (fun _ : Fin k => ν)) ≤
          MultiItemRev.Decomp.BRev (Measure.pi (fun _ : Fin k => ν)) := by sorry

end MultiItemRev.KBundling
