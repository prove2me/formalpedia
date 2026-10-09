-- Prove2me | Theorems.Thm_MultiItemRev_TwoIID_expectation_W_step
-- name    : MultiItemRev.TwoIID.expectation_W_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:29:33.12684+00:00
-- url     : https://prove2.me/theorems/beda0c3f-e4b3-40d5-bd49-c0cd880e5ba8
-- title:
--   Proof of Theorem B, p. 34 — expectation of W at a threshold allocation
-- statement:
--   For independent identically distributed goods $Y,Z$ and a threshold $p\ge0$, take the diagonal allocation $\varphi(t)=\mathbf1_{t\ge p}$ and $\Phi(u)=\max\{u-p,0\}$. With $\Lambda=\min\{Y,Z\}$ and $W=\Lambda\varphi(Y)-\Phi(\Lambda)$,
--
--   $$\mathbb E[W]=\Pr[Y\ge p]\,\mathbb E[\min\{Z,p\}].$$
--
--   This evaluates the nonnegative term in equation (12) for the extreme threshold allocations.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 34, proof of Theorem B, display for E[W]

import Mathlib
import Definitions.Def_MultiItemRev_TwoIID_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.TwoIID

theorem expectation_W_step (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]
    (p : ℝ≥0) :
    let μ := Measure.pi (fun _ : Fin 2 => ν)
    (∫⁻ x, ENNReal.ofReal
      (((min (x 0) (x 1) : ℝ≥0) : ℝ) * (if p ≤ x 0 then 1 else 0) -
        max ((((min (x 0) (x 1) : ℝ≥0) : ℝ) - (p : ℝ))) 0) ∂μ) =
      ν {t | p ≤ t} * ∫⁻ t, ((min t p : ℝ≥0) : ℝ≥0∞) ∂ν := by sorry

end MultiItemRev.TwoIID
