-- Prove2me | Theorems.Thm_MultiItemRev_TwoIID_zeta_le
-- name    : MultiItemRev.TwoIID.zeta_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:29:35.246665+00:00
-- url     : https://prove2.me/theorems/2369c148-dfea-47e3-9b9a-4e986ecacf6f
-- title:
--   Proof of Theorem B, pp. 34–35 — zeta(p) at most r/e
-- statement:
--   Let $X$ have a nonnegative one-good probability law with finite optimal revenue $r$, and write $G(p)=\Pr[X\ge p]$. For every price $p\ge0$, define $\zeta(p)=G(p)(\mathbb E[\min\{X,p\}]-r)$. Then
--
--   $$\zeta(p)\le\frac r e.$$
--
--   This is the numerical estimate used to close the proof of Theorem B.
--
--   **Formalization Note** The truncation $\min\{X,p\}$ is bounded, so its real-valued expectation exists for every finite $p$.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, pp. 34–35, proof of Theorem B after equation (13)

import Mathlib
import Definitions.Def_MultiItemRev_TwoIID_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.TwoIID

theorem zeta_le (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]
    (hr : MultiItemRev.Decomp.Rev1 ν ≠ ⊤) (p : ℝ≥0) :
    let r := (MultiItemRev.Decomp.Rev1 ν).toReal
    (ν {t | p ≤ t}).toReal *
      ((∫ t, ((min t p : ℝ≥0) : ℝ) ∂ν) - r) ≤ r / Real.exp 1 := by sorry

end MultiItemRev.TwoIID
