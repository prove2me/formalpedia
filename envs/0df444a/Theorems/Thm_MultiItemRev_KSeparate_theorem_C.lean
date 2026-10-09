-- Prove2me | Theorems.Thm_MultiItemRev_KSeparate_theorem_C
-- name    : MultiItemRev.KSeparate.theorem_C
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:28:54.407079+00:00
-- url     : https://prove2.me/theorems/2a7160d3-e6cc-438a-ad25-080201144b9b
-- title:
--   Theorem C, p. 7 — separate selling gives a logarithmic-squared guarantee
-- statement:
--   There is an absolute constant $c>0$ such that for every $k\ge2$ and every family of $k$ independent nonnegative goods $X_1,\ldots,X_k$,
--
--   $$\operatorname{SRev}(X_1,\ldots,X_k)\ge\frac{c}{(\log k)^2}\operatorname{Rev}(X_1,\ldots,X_k).$$
--
--   The constant is independent of both the number and the distributions of the goods. This is the paper's separate-selling approximation guarantee in the inequality form established in its proof. **Formalization Note** The laws form a product measure, and revenue can be infinite; multiplication by the positive real coefficient is interpreted in extended nonnegative reals.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 7, Theorem C; p. 26, proof of Theorem C

import Mathlib
import Definitions.Def_MultiItemRev_KSeparate_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.KSeparate

theorem theorem_C :
    ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ), 2 ≤ k →
      ∀ (ν : Fin k → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (ν i)],
        ENNReal.ofReal (c / Real.log (k : ℝ) ^ 2) *
          MultiItemRev.Decomp.Rev (Measure.pi ν) ≤ MultiItemRev.Decomp.SRev (Measure.pi ν) := by sorry

end MultiItemRev.KSeparate
