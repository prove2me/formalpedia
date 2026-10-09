-- Prove2me | Theorems.Thm_MultiItemRev_KSeparate_proposition_13_ii
-- name    : MultiItemRev.KSeparate.proposition_13_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:28:53.563774+00:00
-- url     : https://prove2.me/theorems/f398b25d-a8d7-4aae-a84c-6af61c719296
-- title:
--   Proposition 13(ii), p. 23 — separate revenue versus bundled revenue
-- statement:
--   There is an absolute constant $c>0$ such that for every $k\ge2$ and every family of $k$ independent nonnegative goods $X_1,\ldots,X_k$,
--
--   $$\operatorname{SRev}(X_1,\ldots,X_k)\ge\frac{c}{\log k}\operatorname{BRev}(X_1,\ldots,X_k).$$
--
--   This controls the bundle terms in the decomposition used for Theorem C. **Formalization Note** Independence is represented by the product of the $k$ probability laws. The existential constant precedes both $k$ and those laws.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 23, Proposition 13(ii)

import Mathlib
import Definitions.Def_MultiItemRev_KSeparate_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.KSeparate

theorem proposition_13_ii :
    ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ), 2 ≤ k →
      ∀ (ν : Fin k → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (ν i)],
        ENNReal.ofReal (c / Real.log (k : ℝ)) *
          MultiItemRev.Decomp.BRev (Measure.pi ν) ≤ MultiItemRev.Decomp.SRev (Measure.pi ν) := by sorry

end MultiItemRev.KSeparate
