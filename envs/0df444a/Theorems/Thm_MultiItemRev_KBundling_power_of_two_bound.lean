-- Prove2me | Theorems.Thm_MultiItemRev_KBundling_power_of_two_bound
-- name    : MultiItemRev.KBundling.power_of_two_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:11:54.386198+00:00
-- url     : https://prove2.me/theorems/ee1b880c-ca05-426d-9b27-bf240a499ece
-- title:
--   Proof of Theorem D, p. 26 — for k = 2^m ≥ 2 i.i.d. goods: R_k ≤ 4(log₂ k + 1)·B_k
-- statement:
--   For $k$ i.i.d. goods $X_1,\dots,X_k$ with law $\nu$, write $R_k=\mathrm{Rev}(X_1,\dots,X_k)$ and $B_k=\mathrm{BRev}(X_1,\dots,X_k)$.
--
--   **Claim (proof of Theorem D, p. 26).** If $k=2^m\ge2$ is a power of $2$, then
--   $$R_k\le4(\log_2k+1)\,B_k.$$
--
--   This is the power-of-two case of Theorem D with an explicit constant; the general case follows by monotonicity in the number of goods and Proposition 13 (i).
--
--   **Formalization Note** $k=2^m$ with $m\ge1$; $\log_2$ is `Real.logb 2`, as printed, so $\log_2 k=m$.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 26, proof of Theorem D, first paragraph

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.KBundling

theorem power_of_two_bound (m : ℕ) (hm : 1 ≤ m)
    (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] :
    MultiItemRev.Decomp.Rev (Measure.pi (fun _ : Fin (2 ^ m) => ν)) ≤
      ENNReal.ofReal (4 * (Real.logb 2 ((2 ^ m : ℕ) : ℝ) + 1)) *
        MultiItemRev.Decomp.BRev (Measure.pi (fun _ : Fin (2 ^ m) => ν)) := by sorry

end MultiItemRev.KBundling
