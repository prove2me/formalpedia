-- Prove2me | Theorems.Thm_MultiItemRev_TwoIID_rhs12_le
-- name    : MultiItemRev.TwoIID.rhs12_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:29:27.653505+00:00
-- url     : https://prove2.me/theorems/e525cde6-eeba-43ec-89b8-0de94be6925b
-- title:
--   Proof of Theorem B, pp. 33–35 — the right side of (12)
-- statement:
--   Let $Y,Z$ be independent and identically distributed nonnegative valuations with finite one-good optimal revenue $r$. For every nondecreasing function $\varphi:[0,\infty)\to[0,1]$, put $\Phi(u)=\int_0^u\varphi(t)\,dt$, $\Lambda=\min\{Y,Z\}$, and $W=\Lambda\varphi(Y)-\Phi(\Lambda)$. Then
--
--   $$2r-2r\mathbb E[\varphi(Y)]+2\mathbb E[W]\le2r\left(1+\frac1e\right).$$
--
--   This bounds the expression in equation (12) for the full class of monotone diagonal allocation functions, including the zero function.
--
--   **Formalization Note** The right side is a real number. The expectation of nonnegative $W$ is represented by an extended nonnegative integral, so the statement also asserts the finiteness needed for the comparison.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, pp. 33–35, proof of Theorem B, bound on equation (12)

import Mathlib
import Definitions.Def_MultiItemRev_TwoIID_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.TwoIID

theorem rhs12_le (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]
    (hr : MultiItemRev.Decomp.Rev1 ν ≠ ⊤) (φ : ℝ≥0 → ℝ)
    (hφ : Monotone φ) (hφ01 : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1) :
    let μ := Measure.pi (fun _ : Fin 2 => ν)
    let r := (MultiItemRev.Decomp.Rev1 ν).toReal
    ((2 * r - 2 * r * ∫ t, φ t ∂ν : ℝ) : EReal) +
      2 * ((∫⁻ x, ENNReal.ofReal
        (((min (x 0) (x 1) : ℝ≥0) : ℝ) * φ (x 0) -
          ∫ t in (0 : ℝ)..(((min (x 0) (x 1) : ℝ≥0) : ℝ)), φ t.toNNReal) ∂μ : ℝ≥0∞) : EReal) ≤
        ((2 * r * (1 + 1 / Real.exp 1) : ℝ) : EReal) := by sorry

end MultiItemRev.TwoIID
