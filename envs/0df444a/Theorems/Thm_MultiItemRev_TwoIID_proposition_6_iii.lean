-- Prove2me | Theorems.Thm_MultiItemRev_TwoIID_proposition_6_iii
-- name    : MultiItemRev.TwoIID.proposition_6_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:29:34.578011+00:00
-- url     : https://prove2.me/theorems/17e38f6a-2817-4d6b-ab4d-ab7d06d6ef24
-- title:
--   Proposition 6 (iii), p. 14 — no positive transfers suffice
-- statement:
--   For a random valuation of at least one good, restricting to feasible, incentive-compatible, individually rational mechanisms with nonnegative payments does not change optimal revenue:
--
--   $$\operatorname{Rev}(X)=\sup_{\mu\text{ IC, IR, NPT}}R(\mu;X).$$
--
--   This permits the proof of Theorem B to work with payments that are nonnegative everywhere.
--
--   **Formalization Note** The random valuation is represented by a probability law. Payment measurability is part of admissibility, as allowed by footnote 12, and the two suprema use extended nonnegative revenue values.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 14, Proposition 6 (iii)

import Mathlib
import Definitions.Def_MultiItemRev_TwoIID_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.TwoIID

theorem proposition_6_iii {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : Measure (ι → ℝ≥0)) [IsProbabilityMeasure μ] :
    Rev μ = ⨆ (M : MultiItemRev.Decomp.Mechanism ι) (_ : IsAdmissible M ∧ MultiItemRev.Decomp.IsNPT M),
      (expRevenue μ M).toENNReal := by sorry

end MultiItemRev.TwoIID
