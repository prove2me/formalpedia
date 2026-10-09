-- Prove2me | Theorems.Thm_MultiItemRev_KBundling_proposition_14_ii
-- name    : MultiItemRev.KBundling.proposition_14_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:12:03.926585+00:00
-- url     : https://prove2.me/theorems/dde0e867-c438-4ff6-a004-202d3a662ef3
-- title:
--   Proposition 14 (ii), p. 24 — k ≥ 1 i.i.d. goods: BRev(X₁, …, X_k) ≥ (1/4)·SRev(X₁, …, X_k)
-- statement:
--   **Proposition 14 (ii).** For any $k\ge1$ and any $k$ i.i.d. goods $X_1,\dots,X_k$ (each with law $\nu$),
--   $$\mathrm{BRev}(X_1,\dots,X_k)\ge\frac14\,\mathrm{SRev}(X_1,\dots,X_k).$$
--
--   For identically distributed goods, bundling loses at most a factor $4$ against separate selling. In the proof of Theorem D it bounds each term $(k/\ell)B_\ell$ by $4B_k$.
--
--   **Formalization Note** The $k$ i.i.d. goods have the product law `Measure.pi (fun _ : Fin k => ν)`. At $k=1$ the two revenues coincide.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 24, Proposition 14 (ii)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.KBundling

theorem proposition_14_ii (k : ℕ) (hk : 1 ≤ k)
    (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] :
    ENNReal.ofReal (1 / 4) * MultiItemRev.Decomp.SRev (Measure.pi (fun _ : Fin k => ν)) ≤
      MultiItemRev.Decomp.BRev (Measure.pi (fun _ : Fin k => ν)) := by sorry

end MultiItemRev.KBundling
