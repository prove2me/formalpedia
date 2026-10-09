-- Prove2me | Theorems.Thm_MultiItemRev_TwoIID_theorem_B
-- name    : MultiItemRev.TwoIID.theorem_B
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:30:54.414986+00:00
-- url     : https://prove2.me/theorems/eaa7a957-ae40-4c57-903e-5b671eb55a8c
-- title:
--   Theorem B, p. 6 — separate selling earns at least e/(e+1) of optimal revenue
-- statement:
--   Let two goods have independent, identically distributed nonnegative valuations with common probability law $\nu$. Their joint optimal revenue is at most $(e+1)/e$ times the sum of the two one-good optimal revenues:
--
--   $$\operatorname{Rev}(Y,Z)\le\frac{e+1}{e}\bigl(\operatorname{Rev}(Y)+\operatorname{Rev}(Z)\bigr).$$
--
--   Thus separate selling guarantees at least $e/(e+1)$ of the optimal revenue, including cases where the one-good revenue is zero or infinite.
--
--   **Formalization Note** The two-good law is the product of the common one-good law. The conclusion uses extended nonnegative revenue and the exact constant $(e+1)/e$; no finiteness assumption is placed on the one-good revenue.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 6, Theorem B; p. 31, first display of its proof

import Mathlib
import Definitions.Def_MultiItemRev_TwoIID_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.TwoIID

theorem theorem_B (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] :
    Rev (Measure.pi (fun _ : Fin 2 => ν)) ≤
      ENNReal.ofReal ((Real.exp 1 + 1) / Real.exp 1) * (MultiItemRev.Decomp.Rev1 ν + MultiItemRev.Decomp.Rev1 ν) := by sorry

end MultiItemRev.TwoIID
