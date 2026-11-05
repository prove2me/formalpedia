-- Prove2me | Theorems.Thm_LiquidWelfareFPA_lambda2_mem_Ioo
-- name    : LiquidWelfareFPA.lambda2_mem_Ioo
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:32:25.407646+00:00
-- url     : https://prove2.me/theorems/1775d34d-cc9a-460d-a252-d1fd3a303d43
-- title:
--   Appendix A, p.21 — $\lambda_2\in(0,1)$ for $\gamma\ge1$
-- statement:
--   For every $\gamma\ge1$, with $W$ the principal Lambert $W$ function,
--
--   $$-\frac1\gamma\ <\ W\!\left(-\frac{e^{-2/\gamma}}{\gamma}\right)\ <\ 0,\qquad\text{hence}\qquad 0<\lambda_2=\gamma W\!\left(-\frac{e^{-2/\gamma}}{\gamma}\right)+1<1 .$$
--
--   So $\lambda_2$ is an admissible multiplier in the aggregated inequality of the proof of Theorem 4.2.
--
--   Differences from the source: none.
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, Appendix A, p.21

import Mathlib
import Definitions.Def_LiquidWelfareFPA_lam2

namespace LiquidWelfareFPA

/-- **`λ₂ ∈ (0,1)` for `γ ≥ 1`.**
Fikioris & Tardos, arXiv:2210.07502v4, Appendix A, p.21: "To prove that λ2 = γW(−e^{−2/γ}/γ) + 1
∈ (0, 1), we first note that W(x) is an increasing function in x and that W(x) ∈ (−1, 0) when
x ∈ (−1/e, 0). This immediately proves that λ2 < 1. We now notice that W(−e^{−2/γ}/γ) >
W(−e^{−1/γ}/γ) = −1/γ … This proves that λ2 > 0."

For every `γ ≥ 1`: `−1/γ < W(−e^{−2/γ}/γ) < 0`, and `0 < λ₂(γ) < 1`. -/
theorem lambda2_mem_Ioo (γ : ℝ) (hγ : 1 ≤ γ) :
    -1 / γ < lambertW (-Real.exp (-2 / γ) / γ) ∧ lambertW (-Real.exp (-2 / γ) / γ) < 0 ∧
      0 < lam2 γ ∧ lam2 γ < 1 := by sorry

end LiquidWelfareFPA
