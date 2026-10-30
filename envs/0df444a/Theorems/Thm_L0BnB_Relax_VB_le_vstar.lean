-- Prove2me | Theorems.Thm_L0BnB_Relax_VB_le_vstar
-- name    : L0BnB.Relax.VB_le_vstar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:52:31.328126+00:00
-- url     : https://prove2.me/theorems/48dee849-a801-428b-9502-33111f5328ca
-- title:
--   Eq. (41): $v^*(M)\ge V_{B(M)}$ for $M\ge\sqrt{\lambda_0/\lambda_2}$
-- statement:
--   Let $X\in\mathbb R^{n\times p}$, $y\in\mathbb R^n$, $\lambda_0,\lambda_2>0$ and $M\ge\sqrt{\lambda_0/\lambda_2}$. Then
--
--   $$V_{B(M)}\le v^*(M)=\min_{\|\beta\|_\infty\le M}G(\beta).$$
--
--   This compares the Big-M relaxation with the perspective relaxation restricted to the Big-M box.
--
--   Differences from the source:
--   - encoding: λ0, λ2 regularization parameters "specified by the practitioner" (p. 2), no sign stated → hypotheses 0 < lam0 and 0 < lam2; reason: paper.md Reading 1: √(λ0/λ2), √(λ2/λ0) and ψ1 are undefined otherwise, and L(M) ⊆ (0, ∞) by (9); only undefined cases are excluded
--   - encoding: V_B(M), V_PR(∞): "optimal objective" of the interval relaxations → sInf of the objective values over the relaxation's feasible set (VB, VPRinf); reason: paper.md Reading 3: the feasible sets are nonempty and the objectives ≥ 0, and both minima are attained, so the infimum is the paper's minimum
--   - encoding: v∗(M) = min_{‖β‖∞≤M} G(β) → sInf of G over {β | ∀ i, |β i| ≤ M}; reason: the box is nonempty and compact for M > 0 and G is continuous, so the infimum is the minimum
--   - reading: p. 5: M > 0 such that an optimal solution β∗ of (1) satisfies ‖β∗‖∞ ≤ M; p. 8: "the result of Proposition 2 applies for any M ≥ 0, even if it is mis-specified" → only √(λ0/λ2) ≤ M (which forces M > 0), no hypothesis relating M to an optimal solution of (1); reason: paper.md Reading 2: (41) is a step of the proof of Proposition 2, whose scope the p. 8 remark sets
--   - encoding: ‖y − Xβ‖²₂, ‖β‖²₂, ‖β‖∞ ≤ M, index set [p] = {1, …, p} → sums of squares, ∀ i, |β i| ≤ M, index type Fin p (0-based); reason: paper.md Reading 5; Lean's norm on Fin n → ℝ is the sup norm; no statement depends on the index base
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, proof of (11), eq. (41), p. 29

import Mathlib
import Definitions.Def_L0BnB_Relax_VB
import Definitions.Def_L0BnB_Relax_vstar

namespace L0BnB.Relax

/-- **Eq. (41): `v*(M) ≥ V_B(M)` for `M ≥ √(λ₀/λ₂)`.**
Hazimeh, Mazumder, Saab, *Sparse Regression at Scale: Branch-and-Bound rooted in First-Order
Optimization*, arXiv:2004.06152v2, proof of (11), eq. (41), p. 29: "Define `v∗(M) = min_{‖β‖∞≤M} G(β)` … Suppose that
`M ≥ √(λ0/λ2)`. Then, the following holds: `v∗(M) − V_B(M) ≥ G(β∗) − H(β∗) =
Σ_{i∈[p]} t(β∗i) ≥ 0` (41)".

For `λ₀, λ₂ > 0` and `M ≥ √(λ₀/λ₂)`: `V_B(M) ≤ v*(M)`. -/
theorem VB_le_vstar {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (h0 : 0 < lam0) (h2 : 0 < lam2) (hM : Real.sqrt (lam0 / lam2) ≤ M) :
    VB X y lam0 lam2 M ≤ vstar X y lam0 lam2 M := by sorry

end L0BnB.Relax
