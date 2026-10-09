-- Prove2me | Theorems.Thm_MultiItemRev_TwoIID_display_12
-- name    : MultiItemRev.TwoIID.display_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:29:51.238645+00:00
-- url     : https://prove2.me/theorems/98e19ce6-8aa7-4d2e-b974-12a8b767ca7c
-- title:
--   Equation (12), p. 33 — symmetric mechanism revenue bound
-- statement:
--   Let $Y,Z$ be independent and identically distributed nonnegative valuations with finite one-good optimal revenue $r$. For a symmetric, feasible, incentive-compatible, individually rational mechanism with no positive transfers, put $\varphi(t)=q_1(t,t)$, $\Phi(t)=b(t,t)/2$, $\Lambda=\min\{Y,Z\}$, and $W=\Lambda\varphi(Y)-\Phi(\Lambda)$. Then
--
--   $$R(\mu;(Y,Z))\le 2r-2r\mathbb E[\varphi(Y)]+2\mathbb E[W].$$
--
--   This is the main inequality from which the paper obtains its numerical constant.
--
--   **Formalization Note** The expectation of the nonnegative $W$ is a Lebesgue integral in extended nonnegative reals, while the mechanism's revenue remains extended real. The finiteness hypothesis is used only to express $r$ as a real number.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 33, equation (12)

import Mathlib
import Definitions.Def_MultiItemRev_TwoIID_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.TwoIID

theorem display_12 (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]
    (M : MultiItemRev.Decomp.Mechanism (Fin 2)) (hM : IsAdmissible M ∧ MultiItemRev.Decomp.IsNPT M)
    (hSym : IsSymmetric M) (hr : MultiItemRev.Decomp.Rev1 ν ≠ ⊤) :
    let μ := Measure.pi (fun _ : Fin 2 => ν)
    let r := (MultiItemRev.Decomp.Rev1 ν).toReal
    expRevenue μ M ≤
      ((2 * r - 2 * r * ∫ t, M.q (diag t) 0 ∂ν : ℝ) : EReal) +
        2 * ((∫⁻ x, ENNReal.ofReal
          (((min (x 0) (x 1) : ℝ≥0) : ℝ) * M.q (diag (x 0)) 0 -
            MultiItemRev.Decomp.buyerPayoff M (diag (min (x 0) (x 1))) / 2) ∂μ : ℝ≥0∞) : EReal) := by sorry

end MultiItemRev.TwoIID
