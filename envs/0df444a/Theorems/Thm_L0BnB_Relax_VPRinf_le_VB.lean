-- Prove2me | Theorems.Thm_L0BnB_Relax_VPRinf_le_VB
-- name    : L0BnB.Relax.VPRinf_le_VB
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:51:40.771609+00:00
-- url     : https://prove2.me/theorems/d1964f1e-b179-4ffc-b698-05c72db0707f
-- title:
--   Eq. (10): $V_{B(M)}\ge V_{PR(\infty)}$ if $M\le\frac12\sqrt{\lambda_0/\lambda_2}$
-- statement:
--   Let $X\in\mathbb R^{n\times p}$, $y\in\mathbb R^n$, $\lambda_0,\lambda_2>0$ and $0\le M\le\frac12\sqrt{\lambda_0/\lambda_2}$. Then
--
--   $$V_{B(M)}\ge V_{PR(\infty)} .$$
--
--   For a small Big-M parameter, the Big-M relaxation gives a lower bound at least as strong as the perspective relaxation without Big-M constraints. This is the first half of Proposition 2.
--
--   Differences from the source:
--   - encoding: λ0, λ2 regularization parameters "specified by the practitioner" (p. 2), no sign stated → hypotheses 0 < lam0 and 0 < lam2; reason: paper.md Reading 1: √(λ0/λ2), √(λ2/λ0) and ψ1 are undefined otherwise, and L(M) ⊆ (0, ∞) by (9); only undefined cases are excluded
--   - reading: p. 5: M > 0 such that an optimal solution β∗ of (1) satisfies ‖β∗‖∞ ≤ M; p. 8: "the result of Proposition 2 applies for any M ≥ 0, even if it is mis-specified" → hypothesis 0 ≤ M only, no hypothesis relating M to an optimal solution of (1); reason: paper.md Reading 2: the p. 8 remark sets the scope of Proposition 2; M = 0 is included
--   - encoding: V_B(M), V_PR(∞): "optimal objective" of the interval relaxations → sInf of the objective values over the relaxation's feasible set (VB, VPRinf); reason: paper.md Reading 3: the feasible sets are nonempty and the objectives ≥ 0, and both minima are attained, so the infimum is the paper's minimum
--   - encoding: ‖y − Xβ‖²₂, ‖β‖²₂, ‖β‖∞ ≤ M, index set [p] = {1, …, p} → sums of squares, ∀ i, |β i| ≤ M, index type Fin p (0-based); reason: paper.md Reading 5; Lean's norm on Fin n → ℝ is the sup norm; no statement depends on the index base
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, Proposition 2, eq. (10), p. 7; remark p. 8; proof (39)–(40), p. 29

import Mathlib
import Definitions.Def_L0BnB_Relax_VB
import Definitions.Def_L0BnB_Relax_VPRinf

namespace L0BnB.Relax

/-- **Eq. (10): `V_B(M) ≥ V_PR(∞)` if `M ≤ ½√(λ₀/λ₂)`.**
Hazimeh, Mazumder, Saab, *Sparse Regression at Scale: Branch-and-Bound rooted in First-Order
Optimization*, arXiv:2004.06152v2, Proposition 2, eq. (10), p. 7: "`V_B(M) ≥ V_PR(∞)`, if `M ≤ (1/2)√(λ0/λ2)`"; p. 8: "the
result of Proposition 2 applies for any `M ≥ 0`, even if it is mis-specified." Proof: (40), p. 29.

For every `X, y`, `λ₀, λ₂ > 0` and `0 ≤ M ≤ ½√(λ₀/λ₂)`, the value of the interval relaxation of
PR(∞) is at most that of the interval relaxation of B(M).

**Formalization Note.** `M = 0` is included and no hypothesis ties `M` to an optimal solution of
(1) (paper.md Reading 2). -/
theorem VPRinf_le_VB {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (h0 : 0 < lam0) (h2 : 0 < lam2) (hM : 0 ≤ M)
    (hM2 : M ≤ 1 / 2 * Real.sqrt (lam0 / lam2)) :
    VPRinf X y lam0 lam2 ≤ VB X y lam0 lam2 M := by sorry

end L0BnB.Relax
