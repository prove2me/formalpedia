-- Prove2me | Theorems.Thm_L0BnB_Relax_VPRinf_eq_min_G
-- name    : L0BnB.Relax.VPRinf_eq_min_G
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:48:39.03816+00:00
-- url     : https://prove2.me/theorems/2a91ef58-f791-43a6-8525-d0970cbd6113
-- title:
--   Eq. (6): $V_{PR(\infty)}=\min_\beta G(\beta)$
-- statement:
--   Let $X\in\mathbb R^{n\times p}$, $y\in\mathbb R^n$ and $\lambda_0,\lambda_2>0$. The value of the interval relaxation of PR$(\infty)$ equals the minimum of the reduced objective:
--
--   $$V_{PR(\infty)}=\min_{\beta\in\mathbb R^p}G(\beta),\qquad G(\beta)=\frac12\|y-X\beta\|_2^2+\sum_{i\in[p]}\psi_1(\beta_i;\lambda_0,\lambda_2).$$
--
--   In particular the minimum of $G$ is attained. This eliminates the auxiliary variables $z$, $s$ and is the form in which $V_{PR(\infty)}$ enters the proof of Proposition 2.
--
--   Differences from the source:
--   - encoding: λ0, λ2 regularization parameters "specified by the practitioner" (p. 2), no sign stated → hypotheses 0 < lam0 and 0 < lam2; reason: paper.md Reading 1: √(λ0/λ2), √(λ2/λ0) and ψ1 are undefined otherwise, and L(M) ⊆ (0, ∞) by (9); only undefined cases are excluded
--   - encoding: V_B(M), V_PR(∞): "optimal objective" of the interval relaxations → sInf of the objective values over the relaxation's feasible set (VB, VPRinf); reason: paper.md Reading 3: the feasible sets are nonempty and the objectives ≥ 0, and both minima are attained, so the infimum is the paper's minimum
--   - encoding: "min" in V_PR(∞) = min_{β∈R^p} G(β) → IsLeast of the set of values (attained and a lower bound); reason: IsLeast is exactly the statement that the minimum exists and equals the value
--   - encoding: ‖y − Xβ‖²₂, ‖β‖²₂, ‖β‖∞ ≤ M, index set [p] = {1, …, p} → sums of squares, ∀ i, |β i| ≤ M, index type Fin p (0-based); reason: paper.md Reading 5; Lean's norm on Fin n → ℝ is the sup norm; no statement depends on the index base
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, eq. (6), p. 6

import Mathlib
import Definitions.Def_L0BnB_Relax_G
import Definitions.Def_L0BnB_Relax_VPRinf

namespace L0BnB.Relax

/-- **Eq. (6): `V_PR(∞) = min_β G(β)`.**
Hazimeh, Mazumder, Saab, *Sparse Regression at Scale: Branch-and-Bound rooted in First-Order
Optimization*, arXiv:2004.06152v2, eq. (6), p. 6: "[21] has shown that the interval relaxation of PR(∞) can be written as:
`V_PR(∞) = min_{β∈ℝᵖ} G(β) := (1/2)‖y − Xβ‖²₂ + Σ_{i∈[p]} ψ1(βi; λ0, λ2)`".

For `λ₀, λ₂ > 0`, the optimal value `V_PR(∞)` of the interval relaxation of PR(∞) (an infimum
over `(β, z, s)`) is the least value of `G` on `ℝᵖ`: it is attained by some `β` and
`V_PR(∞) ≤ G(β')` for every `β'`.

**Formalization Note.** "min" is `IsLeast (Set.range G)`, which asserts both the value identity
and attainment. -/
theorem VPRinf_eq_min_G {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 : ℝ) (h0 : 0 < lam0) (h2 : 0 < lam2) :
    IsLeast (Set.range (G X y lam0 lam2)) (VPRinf X y lam0 lam2) := by sorry

end L0BnB.Relax
