-- Prove2me | Theorems.Thm_MultiItemRev_KBundling_rev_mono_goods
-- name    : MultiItemRev.KBundling.rev_mono_goods
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:11:58.030446+00:00
-- url     : https://prove2.me/theorems/669e4e11-1157-4521-bae5-1748689e2fb0
-- title:
--   Proof of Theorem D, p. 27 — adding i.i.d. goods can only increase the revenue: R_k ≤ R_k′, B_k ≤ B_k′ for k ≤ k′
-- statement:
--   With $R_k$ and $B_k$ the optimal and bundled revenues of $k$ i.i.d. goods with law $\nu$:
--
--   **Claim (proof of Theorem D, p. 27).** Adding goods can only increase the revenue: for $k\le k'$,
--   $$R_k\le R_{k'}\qquad\text{and}\qquad B_k\le B_{k'}.$$
--
--   The paper uses it with $2^{m-1}<k<2^m$, in the form $R_k\le R_{2^m}$ and $B_k\ge B_{2^{m-1}}$, to pass from powers of two to all $k$.
--
--   **Formalization Note** Stated for all $k\le k'$, as the parenthetical "adding goods can only increase the revenue" is general; $k=0$ (no goods, revenue $0$) is allowed and true.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 27, proof of Theorem D, parenthetical remark

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.KBundling

theorem rev_mono_goods (k k' : ℕ) (hk : k ≤ k')
    (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] :
    MultiItemRev.Decomp.Rev (Measure.pi (fun _ : Fin k => ν)) ≤ MultiItemRev.Decomp.Rev (Measure.pi (fun _ : Fin k' => ν)) ∧
      MultiItemRev.Decomp.BRev (Measure.pi (fun _ : Fin k => ν)) ≤ MultiItemRev.Decomp.BRev (Measure.pi (fun _ : Fin k' => ν)) := by sorry

end MultiItemRev.KBundling
