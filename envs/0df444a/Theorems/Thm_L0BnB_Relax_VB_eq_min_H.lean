-- Prove2me | Theorems.Thm_L0BnB_Relax_VB_eq_min_H
-- name    : L0BnB.Relax.VB_eq_min_H
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:50:18.908513+00:00
-- url     : https://prove2.me/theorems/e8965903-6457-4f7c-8b95-1813066f3de6
-- title:
--   Eq. (37): $V_{B(M)}=\min_{\|\beta\|_\infty\le M}H(\beta)$
-- statement:
--   Let $X\in\mathbb R^{n\times p}$, $y\in\mathbb R^n$, $\lambda_0,\lambda_2>0$ and $M>0$. The value of the interval relaxation of B$(M)$ is
--
--   $$V_{B(M)}=\min_{\|\beta\|_\infty\le M}H(\beta),\qquad H(\beta)=\frac12\|y-X\beta\|_2^2+\sum_{i\in[p]}\Bigl(\frac{\lambda_0}{M}|\beta_i|+\lambda_2\beta_i^2\Bigr),$$
--
--   and the minimum is attained. This eliminates $z$ from the Big-M relaxation.
--
--   Differences from the source:
--   - encoding: λ0, λ2 regularization parameters "specified by the practitioner" (p. 2), no sign stated → hypotheses 0 < lam0 and 0 < lam2; reason: paper.md Reading 1: √(λ0/λ2), √(λ2/λ0) and ψ1 are undefined otherwise, and L(M) ⊆ (0, ∞) by (9); only undefined cases are excluded
--   - encoding: V_B(M), V_PR(∞): "optimal objective" of the interval relaxations → sInf of the objective values over the relaxation's feasible set (VB, VPRinf); reason: paper.md Reading 3: the feasible sets are nonempty and the objectives ≥ 0, and both minima are attained, so the infimum is the paper's minimum
--   - encoding: "min" in V_B(M) = min_{‖β‖∞≤M} H(β) → IsLeast of the set of values (attained and a lower bound); reason: IsLeast is exactly the statement that the minimum exists and equals the value
--   - encoding: ‖y − Xβ‖²₂, ‖β‖²₂, ‖β‖∞ ≤ M, index set [p] = {1, …, p} → sums of squares, ∀ i, |β i| ≤ M, index type Fin p (0-based); reason: paper.md Reading 5; Lean's norm on Fin n → ℝ is the sup norm; no statement depends on the index base
--   - generalization: p. 5: "We assume that there is a finite scalar M > 0 (a-priori specified) such that an optimal solution of Problem (1), say β∗, satisfies: ‖β∗‖∞ ≤ M" (standing assumption of §2.1, under which Proposition 1 and (37) are stated) → 0 < M only, no hypothesis relating M to an optimal solution of (1); reason: the reduction (37) eliminates z for any M > 0 and never uses that assumption; the proof of Proposition 2 (p. 29) uses (37) for any M, as the p. 8 remark allows; for well-specified M it is the source's claim
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, proof of Proposition 1, eq. (37), p. 28

import Mathlib
import Definitions.Def_L0BnB_Relax_VB
import Definitions.Def_L0BnB_Relax_H

namespace L0BnB.Relax

/-- **Eq. (37): `V_B(M) = min_{‖β‖∞≤M} H(β)`.**
Hazimeh, Mazumder, Saab, *Sparse Regression at Scale: Branch-and-Bound rooted in First-Order
Optimization*, arXiv:2004.06152v2, proof of Proposition 1, eq. (37), p. 28: "Note that `V_B(M)` can be simplified to:
`V_B(M) = min_{‖β‖∞≤M} H(β) := (1/2)‖y − Xβ‖²₂ + Σ_{i∈[p]} ((λ0/M)|βi| + λ2β²i)`."

For `λ₀, λ₂ > 0` and `M > 0`, the optimal value `V_B(M)` of the interval relaxation of B(M) (an
infimum over `(β, z)`) is the least value of `H` on the box `{β : ∀ i, |βᵢ| ≤ M}`.

**Formalization Note.** `M > 0` is the paper's standing assumption on p. 5 and is needed because
`H` contains `λ₀/M`. "min" is `IsLeast` of the image of the box. -/
theorem VB_eq_min_H {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (h0 : 0 < lam0) (h2 : 0 < lam2) (hM : 0 < M) :
    IsLeast (H X y lam0 lam2 M '' {β | ∀ i, |β i| ≤ M}) (VB X y lam0 lam2 M) := by sorry

end L0BnB.Relax
