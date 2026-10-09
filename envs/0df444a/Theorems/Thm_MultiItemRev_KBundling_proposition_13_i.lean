-- Prove2me | Theorems.Thm_MultiItemRev_KBundling_proposition_13_i
-- name    : MultiItemRev.KBundling.proposition_13_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:12:00.738319+00:00
-- url     : https://prove2.me/theorems/ab3df912-c3b6-4038-b124-265b97e34d1a
-- title:
--   Proposition 13 (i), p. 23 — two independent goods: SRev(X₁, X₂) ≥ (1/(w + 1))·BRev(X₁, X₂)
-- statement:
--   Let $w$ be the solution of $w\,e^{w+1}=1$.
--
--   **Proposition 13 (i).** For any two independent goods $X_1,X_2$ (one-good random valuations with laws $\nu_1,\nu_2$),
--   $$\mathrm{SRev}(X_1,X_2)\ge\frac1{w+1}\,\mathrm{BRev}(X_1,X_2).$$
--
--   Selling two independent goods separately earns at least about $78\%$ of the bundled revenue. In the proof of Theorem D it is applied to two i.i.d. blocks of goods, to show $B_{2^m}\le2(w+1)B_{2^{m-1}}$.
--
--   **Formalization Note** The pair $(X_1,X_2)$ with independent coordinates has the product law on `Unit ⊕ Unit → ℝ≥0` (`jointLaw (oneGood ν₁) (oneGood ν₂)`), the same encoding as Theorem A in the sibling missions. $w$ is a parameter with hypothesis $w\,e^{w+1}=1$; the approximation $0.78$ is not part of the statement.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 23, Proposition 13 (i)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.KBundling

theorem proposition_13_i (w : ℝ) (hw : w * Real.exp (w + 1) = 1)
    (ν₁ ν₂ : Measure ℝ≥0) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] :
    ENNReal.ofReal (1 / (w + 1)) * MultiItemRev.Decomp.BRev (MultiItemRev.Decomp.jointLaw (MultiItemRev.Decomp.oneGood ν₁) (MultiItemRev.Decomp.oneGood ν₂)) ≤
      MultiItemRev.Decomp.SRev (MultiItemRev.Decomp.jointLaw (MultiItemRev.Decomp.oneGood ν₁) (MultiItemRev.Decomp.oneGood ν₂)) := by sorry

end MultiItemRev.KBundling
