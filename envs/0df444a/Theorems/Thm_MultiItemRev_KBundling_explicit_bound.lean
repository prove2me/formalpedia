-- Prove2me | Theorems.Thm_MultiItemRev_KBundling_explicit_bound
-- name    : MultiItemRev.KBundling.explicit_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:11:51.75291+00:00
-- url     : https://prove2.me/theorems/f1be9d70-1ffb-4491-98ad-6233f50b5049
-- title:
--   Proof of Theorem D, p. 27 — for k ≥ 2 i.i.d. goods: R_k ≤ 8(w + 1)(log₂ k + 2)·B_k
-- statement:
--   Let $w$ be the solution of $w\,e^{w+1}=1$, and let $R_k$, $B_k$ be the optimal and bundled revenues of $k$ i.i.d. goods with law $\nu$.
--
--   **Claim (proof of Theorem D, p. 27).** For every $k\ge2$,
--   $$R_k\le8(w+1)(\log_2k+2)\,B_k.$$
--
--   This is the explicit form of Theorem D, with the constant made concrete: $c$ of Theorem D can be taken of order $1/(8(w+1))$ up to the change of logarithm base.
--
--   **Formalization Note** $\log_2$ is `Real.logb 2`, as printed; $w$ is a parameter with hypothesis $w\,e^{w+1}=1$.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 27, proof of Theorem D, last sentence

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.KBundling

theorem explicit_bound (w : ℝ) (hw : w * Real.exp (w + 1) = 1)
    (k : ℕ) (hk : 2 ≤ k) (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] :
    MultiItemRev.Decomp.Rev (Measure.pi (fun _ : Fin k => ν)) ≤
      ENNReal.ofReal (8 * (w + 1) * (Real.logb 2 (k : ℝ) + 2)) *
        MultiItemRev.Decomp.BRev (Measure.pi (fun _ : Fin k => ν)) := by sorry

end MultiItemRev.KBundling
