-- Prove2me | Theorems.Thm_L0BnB_Relax_tfun_nonpos_small_M
-- name    : L0BnB.Relax.tfun_nonpos_small_M
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:50:56.928465+00:00
-- url     : https://prove2.me/theorems/2067fa58-ac52-4591-a5b6-825b56f37a8e
-- title:
--   Eq. (39): $t(\beta_i)\le0$ for $M\le\frac12\sqrt{\lambda_0/\lambda_2}$
-- statement:
--   Let $\lambda_0,\lambda_2>0$, $M\le\frac12\sqrt{\lambda_0/\lambda_2}$ and $|b|\le M$. Then
--
--   $$t(b)=\Bigl(2\sqrt{\lambda_0\lambda_2}-\frac{\lambda_0}{M}\Bigr)|b|-\lambda_2b^2\le0 .$$
--
--   Summed over the coordinates of an optimal solution of (37), this gives (40) and hence (10).
--
--   Differences from the source:
--   - encoding: λ0, λ2 regularization parameters "specified by the practitioner" (p. 2), no sign stated → hypotheses 0 < lam0 and 0 < lam2; reason: paper.md Reading 1: √(λ0/λ2), √(λ2/λ0) and ψ1 are undefined otherwise, and L(M) ⊆ (0, ∞) by (9); only undefined cases are excluded
--   - generalization: M > 0 (standing assumption, p. 5) → no sign hypothesis on M; reason: |b| ≤ M forces M ≥ 0, and at M = 0 it forces b = 0, where both sides are 0 (Lean's λ0/0 = 0 multiplies |b| = 0); for M > 0 it is the source's claim
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, proof of (10), eq. (39), p. 29

import Mathlib
import Definitions.Def_L0BnB_Relax_tfun

namespace L0BnB.Relax

/-- **Eq. (39): `t(βᵢ) ≤ 0` when `M ≤ ½√(λ₀/λ₂)` and `|βᵢ| ≤ M`.**
Hazimeh, Mazumder, Saab, *Sparse Regression at Scale: Branch-and-Bound rooted in First-Order
Optimization*, arXiv:2004.06152v2, proof of (10), eq. (39), p. 29: "Suppose that `M ≤ (1/2)√(λ0/λ2)` and `|βi| ≤ M`. Using
the fact that `|βi| ≤ √(λ0/λ2)` and the definition of B, we have `B(βi√(λ2/λ0)) =
√(λ2/λ0)|βi|`. This leads to: `t(βi) = (2√(λ0λ2) − λ0/M)|βi| − λ2β²i ≤ 0`, (39)".

For `λ₀, λ₂ > 0`, `M ≤ ½√(λ₀/λ₂)` and `|b| ≤ M`:
`t(b) = (2√(λ₀λ₂) − λ₀/M)|b| − λ₂ b²` and `t(b) ≤ 0`.

**Formalization Note.** No sign hypothesis on `M` is needed: `|b| ≤ M` forces `M ≥ 0`, and at
`M = 0` it forces `b = 0`, where both sides vanish (Lean's `λ₀/0 = 0` multiplies `|b| = 0`). -/
theorem tfun_nonpos_small_M (lam0 lam2 M b : ℝ) (h0 : 0 < lam0) (h2 : 0 < lam2)
    (hM : M ≤ 1 / 2 * Real.sqrt (lam0 / lam2)) (hb : |b| ≤ M) :
    tfun lam0 lam2 M b = (2 * Real.sqrt (lam0 * lam2) - lam0 / M) * |b| - lam2 * b ^ 2 ∧
      tfun lam0 lam2 M b ≤ 0 := by sorry

end L0BnB.Relax
