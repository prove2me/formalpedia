-- Prove2me | Theorems.Thm_L0BnB_DualGap_alphaStar_norm_le_one
-- name    : L0BnB.DualGap.alphaStar_norm_le_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:29:55.323049+00:00
-- url     : https://prove2.me/theorems/8e62b1cf-c09a-4777-bd5d-e85905bb6ef3
-- title:
--   Proof of Lemma 2 — ‖α∗‖2 ≤ 1
-- statement:
--   Let $X\in\mathbb R^{n\times p}$, $y\in\mathbb R^n$ with $\|y\|_2=1$, $\lambda_0,\lambda_2,M>0$, and let $\beta^*$ be an optimal solution of (5). With $r^*=y-X\beta^*$ and $\alpha^*=-r^*$,
--   $$
--   \|\alpha^*\|_2\le 1 .
--   $$
--
--   This bound on the optimal dual variable $\alpha^*$ (defined by formula (23)) is used twice in the analysis of the dual bounds: in Lemma 2 and in (53).
--
--   **Formalization Note** No assumption on the columns of $X$ and no restriction on the regime of $\sqrt{\lambda_0/\lambda_2}$ versus $M$ is needed; both regimes of $\psi$ are covered.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 32, Proof of Lemma 2 (‖α∗‖2 ≤ 1)

import Mathlib
import Definitions.Def_L0BnB_DualGap_Setup
import Definitions.Def_L0BnB_DualGap_Duals

namespace L0BnB.DualGap

/-- Proof of Lemma 2, p. 32: if `‖y‖₂ = 1` and `β*` is optimal for (5), then `α* = −r*` satisfies
`½‖α*‖₂² = ½‖r*‖₂² ≤ F(β*) ≤ F(0) = ½‖y‖₂² = ½`, hence `‖α*‖₂ ≤ 1`. -/
theorem alphaStar_norm_le_one {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hy : ∑ r, y r ^ 2 = 1) (βs : Fin p → ℝ) (hβs : IsOptimal X y lam0 lam2 M βs) :
    Real.sqrt (∑ r, L0BnB.Duality.alphaStar X y βs r ^ 2) ≤ 1 := by sorry

end L0BnB.DualGap
