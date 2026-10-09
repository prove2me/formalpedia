-- Prove2me | Theorems.Thm_MultiItemRev_KSeparate_theorem_A
-- name    : MultiItemRev.KSeparate.theorem_A
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:28:56.201991+00:00
-- url     : https://prove2.me/theorems/85ce58e8-33fa-488b-a13d-ee29dea0337e
-- title:
--   Theorem A as (2), p. 16 — two independent goods
-- statement:
--   For two independent nonnegative one-good valuations $Y$ and $Z$,
--
--   $$\operatorname{Rev}(Y,Z)\le2\bigl(\operatorname{Rev}(Y)+\operatorname{Rev}(Z)\bigr).$$
--
--   This is the two-good base case for the power-of-two induction in Theorem C. **Formalization Note** Each one-good law is lifted to a singleton coordinate type, and the two laws are combined by a product.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 16, Theorem A, display (2)

import Mathlib
import Definitions.Def_MultiItemRev_KSeparate_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.KSeparate

theorem theorem_A (ν₁ ν₂ : Measure ℝ≥0)
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] :
    MultiItemRev.Decomp.Rev (MultiItemRev.Decomp.jointLaw (MultiItemRev.Decomp.oneGood ν₁) (MultiItemRev.Decomp.oneGood ν₂)) ≤
      2 * (MultiItemRev.Decomp.Rev1 ν₁ + MultiItemRev.Decomp.Rev1 ν₂) := by sorry

end MultiItemRev.KSeparate
