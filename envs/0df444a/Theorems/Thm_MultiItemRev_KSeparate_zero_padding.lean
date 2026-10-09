-- Prove2me | Theorems.Thm_MultiItemRev_KSeparate_zero_padding
-- name    : MultiItemRev.KSeparate.zero_padding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:28:52.746234+00:00
-- url     : https://prove2.me/theorems/d89f3b08-751a-4754-9f61-8b70f64be7a4
-- title:
--   Proof of Theorem C, p. 26 — zero-valued goods do not change optimal revenue
-- statement:
--   Let $X_1,\ldots,X_k$ be independent nonnegative goods. Append any finite number of goods that are identically zero. Then
--
--   $$\operatorname{Rev}(X_1,\ldots,X_k,0,\ldots,0)=\operatorname{Rev}(X_1,\ldots,X_k).$$
--
--   This permits comparison with a power-of-two number of goods in the final step of Theorem C. **Formalization Note** The zero-valued goods have Dirac laws at zero; the statement includes zero or more appended goods.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 26, proof of Theorem C, zero-padding sentence

import Mathlib
import Definitions.Def_MultiItemRev_KSeparate_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.KSeparate

theorem zero_padding (k j : ℕ) (ν : Fin k → Measure ℝ≥0)
    [∀ i, IsProbabilityMeasure (ν i)] :
    MultiItemRev.Decomp.Rev (Measure.pi (Fin.append ν (fun _ : Fin j => Measure.dirac 0))) =
      MultiItemRev.Decomp.Rev (Measure.pi ν) := by sorry

end MultiItemRev.KSeparate
