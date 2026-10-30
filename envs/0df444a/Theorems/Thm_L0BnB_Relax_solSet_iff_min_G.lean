-- Prove2me | Theorems.Thm_L0BnB_Relax_solSet_iff_min_G
-- name    : L0BnB.Relax.solSet_iff_min_G
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:49:28.912581+00:00
-- url     : https://prove2.me/theorems/2a6ec27f-232c-4d8d-843e-3beb6b48b428
-- title:
--   $\mathcal S(\lambda_2)$ is the set of minimizers of $G$ (proof of (11), p. 30)
-- statement:
--   Let $\lambda_0,\lambda_2>0$. A vector $\beta\in\mathbb R^p$ belongs to $\mathcal S(\lambda_2)$, the set of optimal $\beta$'s of the interval relaxation of PR$(\infty)$, if and only if
--
--   $$G(\beta)\le G(\beta')\qquad\text{for all }\beta'\in\mathbb R^p .$$
--
--   The proof of (11) uses this identification ("$\hat\beta\in\mathcal S(\lambda_2)$, i.e., $\hat\beta$ is optimal for (6)").
--
--   Differences from the source:
--   - encoding: λ0, λ2 regularization parameters "specified by the practitioner" (p. 2), no sign stated → hypotheses 0 < lam0 and 0 < lam2; reason: paper.md Reading 1: √(λ0/λ2), √(λ2/λ0) and ψ1 are undefined otherwise, and L(M) ⊆ (0, ∞) by (9); only undefined cases are excluded
--   - reading: S(λ2): "the set of optimal solutions (in β) of the interval relaxation of PR(∞)" → solSet: β with some (z, s) such that (β, z, s) is feasible and its objective is ≤ that of every feasible point; reason: paper.md Reading 4: the literal β-projection of the optimal set, written without the infimum
--   - encoding: ‖y − Xβ‖²₂, ‖β‖²₂, ‖β‖∞ ≤ M, index set [p] = {1, …, p} → sums of squares, ∀ i, |β i| ≤ M, index type Fin p (0-based); reason: paper.md Reading 5; Lean's norm on Fin n → ℝ is the sup norm; no statement depends on the index base
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, proof of Proposition 2, p. 30

import Mathlib
import Definitions.Def_L0BnB_Relax_G
import Definitions.Def_L0BnB_Relax_solSet

namespace L0BnB.Relax

/-- **`S(λ₂)` is the set of minimizers of `G`** (proof of (11), p. 30).
Hazimeh, Mazumder, Saab, *Sparse Regression at Scale: Branch-and-Bound rooted in First-Order
Optimization*, arXiv:2004.06152v2, proof of Proposition 2, p. 30: "Now suppose that `λ2 ∈ L(M)` (defined in (9)) and let
`β̂ ∈ S(λ2)` (i.e., `β̂` is optimal for (6)) be such that it satisfies `‖β̂‖∞ ≤ M`."

For `λ₀, λ₂ > 0`, a vector `β` lies in `S(λ₂)` (it is the β-part of an optimal solution of the
interval relaxation of PR(∞)) if and only if `β` minimizes `G` over `ℝᵖ`. -/
theorem solSet_iff_min_G {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 : ℝ) (h0 : 0 < lam0) (h2 : 0 < lam2) (β : Fin p → ℝ) :
    β ∈ solSet X y lam0 lam2 ↔ ∀ β' : Fin p → ℝ, G X y lam0 lam2 β ≤ G X y lam0 lam2 β' := by sorry

end L0BnB.Relax
