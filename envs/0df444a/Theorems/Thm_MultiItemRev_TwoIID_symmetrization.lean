-- Prove2me | Theorems.Thm_MultiItemRev_TwoIID_symmetrization
-- name    : MultiItemRev.TwoIID.symmetrization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:30:32.669979+00:00
-- url     : https://prove2.me/theorems/4e6e01d9-5e73-4d5b-b6e0-798c23cf7ce2
-- title:
--   Proof of Theorem B, p. 32 — symmetrizing a two-good mechanism
-- statement:
--   Let two goods have the same one-good probability law and independent values. Average a feasible, incentive-compatible, individually rational, no-positive-transfer mechanism with its copy obtained by exchanging the goods. The resulting mechanism has the same four properties, is symmetric, and yields the same expected payment:
--
--   $$R(\bar\mu;(Y,Z))=R(\mu;(Y,Z)).$$
--
--   Symmetrization permits the later estimates to use identical diagonal allocation coordinates.
--
--   **Formalization Note** Independence and identical distribution are encoded by the product law on two coordinates. Measurability of the payment is part of admissibility.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 32, proof of Theorem B, symmetrization paragraph

import Mathlib
import Definitions.Def_MultiItemRev_TwoIID_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.TwoIID

theorem symmetrization (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]
    (M : MultiItemRev.Decomp.Mechanism (Fin 2)) (hM : IsAdmissible M ∧ MultiItemRev.Decomp.IsNPT M) :
    IsAdmissible (symmetrize M) ∧ MultiItemRev.Decomp.IsNPT (symmetrize M) ∧
      IsSymmetric (symmetrize M) ∧
      expRevenue (Measure.pi (fun _ : Fin 2 => ν)) (symmetrize M) =
        expRevenue (Measure.pi (fun _ : Fin 2 => ν)) M := by sorry

end MultiItemRev.TwoIID
