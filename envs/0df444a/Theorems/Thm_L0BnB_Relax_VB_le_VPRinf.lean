-- Prove2me | Theorems.Thm_L0BnB_Relax_VB_le_VPRinf
-- name    : L0BnB.Relax.VB_le_VPRinf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:53:13.864242+00:00
-- url     : https://prove2.me/theorems/8396f279-4864-432c-94cd-55e2967a7371
-- title:
--   Eq. (11): $V_{B(M)}\le V_{PR(\infty)}$ if $M\ge\sqrt{\lambda_0/\lambda_2}$ and $\lambda_2\in\mathcal L(M)$
-- statement:
--   Let $X\in\mathbb R^{n\times p}$, $y\in\mathbb R^n$, $\lambda_0>0$ and $M\ge\sqrt{\lambda_0/\lambda_2}$, and suppose $\lambda_2\in\mathcal L(M)$, that is, $\lambda_2>0$ and some optimal $\beta$ of the interval relaxation of PR$(\infty)$ satisfies $\|\beta\|_\infty\le M$. Then
--
--   $$V_{B(M)}\le V_{PR(\infty)} .$$
--
--   For a large Big-M parameter, the perspective relaxation is at least as strong. This is the second half of Proposition 2.
--
--   Differences from the source:
--   - encoding: λ0 regularization parameter, no sign stated (p. 2) → hypothesis 0 < lam0 (0 < lam2 is carried by lam2 ∈ L(M)); reason: paper.md Reading 1: √(λ0/λ2) is undefined otherwise; only undefined cases are excluded
--   - reading: p. 5: M > 0 such that an optimal solution β∗ of (1) satisfies ‖β∗‖∞ ≤ M; p. 8: "the result of Proposition 2 applies for any M ≥ 0, even if it is mis-specified" → only √(λ0/λ2) ≤ M (which forces M > 0), no hypothesis relating M to an optimal solution of (1); reason: paper.md Reading 2: the p. 8 remark sets the scope of Proposition 2
--   - encoding: V_B(M), V_PR(∞): "optimal objective" of the interval relaxations → sInf of the objective values over the relaxation's feasible set (VB, VPRinf); reason: paper.md Reading 3: the feasible sets are nonempty and the objectives ≥ 0, and both minima are attained, so the infimum is the paper's minimum
--   - reading: S(λ2): "the set of optimal solutions (in β) of the interval relaxation of PR(∞)" → solSet: β with some (z, s) such that (β, z, s) is feasible and its objective is ≤ that of every feasible point; reason: paper.md Reading 4: the literal β-projection of the optimal set, written without the infimum
--   - encoding: ‖y − Xβ‖²₂, ‖β‖²₂, ‖β‖∞ ≤ M, index set [p] = {1, …, p} → sums of squares, ∀ i, |β i| ≤ M, index type Fin p (0-based); reason: paper.md Reading 5; Lean's norm on Fin n → ℝ is the sup norm; no statement depends on the index base
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, Proposition 2, eq. (11), p. 7; remark p. 8; proof pp. 29–30

import Mathlib
import Definitions.Def_L0BnB_Relax_VB
import Definitions.Def_L0BnB_Relax_VPRinf
import Definitions.Def_L0BnB_Relax_Lset

namespace L0BnB.Relax

/-- **Eq. (11): `V_B(M) ≤ V_PR(∞)` if `M ≥ √(λ₀/λ₂)` and `λ₂ ∈ L(M)`.**
Hazimeh, Mazumder, Saab, *Sparse Regression at Scale: Branch-and-Bound rooted in First-Order
Optimization*, arXiv:2004.06152v2, Proposition 2, eq. (11), p. 7: "`V_B(M) ≤ V_PR(∞)`, if `M ≥ √(λ0/λ2)` and `λ2 ∈ L(M)`."
Proof p. 30.

For every `X, y`, `λ₀ > 0` and `M` with `M ≥ √(λ₀/λ₂)` and `λ₂ ∈ L(M)` (so `λ₂ > 0` and some
optimal β of the PR(∞) relaxation satisfies `‖β‖∞ ≤ M`): `V_B(M) ≤ V_PR(∞)`.

**Formalization Note.** `0 < λ₂` is not a separate hypothesis: it is part of `λ₂ ∈ L(M)` by (9). -/
theorem VB_le_VPRinf {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (h0 : 0 < lam0) (hM : Real.sqrt (lam0 / lam2) ≤ M)
    (hL : lam2 ∈ Lset X y lam0 M) :
    VB X y lam0 lam2 M ≤ VPRinf X y lam0 lam2 := by sorry

end L0BnB.Relax
