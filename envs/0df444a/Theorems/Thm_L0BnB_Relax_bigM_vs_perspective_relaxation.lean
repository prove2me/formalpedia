-- Prove2me | Theorems.Thm_L0BnB_Relax_bigM_vs_perspective_relaxation
-- name    : L0BnB.Relax.bigM_vs_perspective_relaxation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:54:08.029844+00:00
-- url     : https://prove2.me/theorems/a5709a6c-a098-4977-92dd-b4296a164d83
-- title:
--   Proposition 2: Big-M versus perspective relaxation, (10) and (11)
-- statement:
--   Let $X\in\mathbb R^{n\times p}$, $y\in\mathbb R^n$, $\lambda_0>0$, $\lambda_2>0$ and $M\ge0$. Let $V_{B(M)}$ be the optimal value of the interval relaxation of the Big-M formulation (2), $V_{PR(\infty)}$ that of the perspective formulation (3) with $M=\infty$, and $\mathcal L(M)$ the set (9). Then
--
--   1. $$V_{B(M)}\ge V_{PR(\infty)}\quad\text{if } M\le\tfrac12\sqrt{\lambda_0/\lambda_2},\qquad(10)$$
--   2. $$V_{B(M)}\le V_{PR(\infty)}\quad\text{if } M\ge\sqrt{\lambda_0/\lambda_2}\text{ and }\lambda_2\in\mathcal L(M).\qquad(11)$$
--
--   No assumption relates $M$ to an optimal solution of problem (1): the comparison holds for every $M\ge0$, including a mis-specified one. With the other parameters fixed, a small $\lambda_2$ favors the Big-M relaxation and a large $\lambda_2$ the perspective relaxation.
--
--   Differences from the source:
--   - encoding: λ0, λ2 regularization parameters "specified by the practitioner" (p. 2), no sign stated → hypotheses 0 < lam0 and 0 < lam2; reason: paper.md Reading 1: √(λ0/λ2), √(λ2/λ0) and ψ1 are undefined otherwise, and L(M) ⊆ (0, ∞) by (9); only undefined cases are excluded
--   - reading: p. 5: M > 0 such that an optimal solution β∗ of (1) satisfies ‖β∗‖∞ ≤ M; p. 8: "the result of Proposition 2 applies for any M ≥ 0, even if it is mis-specified" → hypothesis 0 ≤ M only, no hypothesis relating M to an optimal solution of (1); reason: paper.md Reading 2: the p. 8 remark sets the scope of Proposition 2; M = 0 is included
--   - encoding: V_B(M), V_PR(∞): "optimal objective" of the interval relaxations → sInf of the objective values over the relaxation's feasible set (VB, VPRinf); reason: paper.md Reading 3: the feasible sets are nonempty and the objectives ≥ 0, and both minima are attained, so the infimum is the paper's minimum
--   - reading: S(λ2): "the set of optimal solutions (in β) of the interval relaxation of PR(∞)" → solSet: β with some (z, s) such that (β, z, s) is feasible and its objective is ≤ that of every feasible point; reason: paper.md Reading 4: the literal β-projection of the optimal set, written without the infimum
--   - encoding: ‖y − Xβ‖²₂, ‖β‖²₂, ‖β‖∞ ≤ M, index set [p] = {1, …, p} → sums of squares, ∀ i, |β i| ≤ M, index type Fin p (0-based); reason: paper.md Reading 5; Lean's norm on Fin n → ℝ is the sup norm; no statement depends on the index base
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, Proposition 2, eqs. (9)–(11), p. 7; remark p. 8; proof pp. 29–30

import Mathlib
import Definitions.Def_L0BnB_Relax_VB
import Definitions.Def_L0BnB_Relax_VPRinf
import Definitions.Def_L0BnB_Relax_Lset

namespace L0BnB.Relax

/-- **Proposition 2 (Big-M versus perspective relaxation).**
Hazimeh, Mazumder, Saab, *Sparse Regression at Scale: Branch-and-Bound rooted in First-Order
Optimization*, arXiv:2004.06152v2, Proposition 2, p. 7: "Let `L(M)` be as defined in (9). Then, the following holds:
`V_B(M) ≥ V_PR(∞)`, if `M ≤ (1/2)√(λ0/λ2)` (10); `V_B(M) ≤ V_PR(∞)`, if `M ≥ √(λ0/λ2)` and
`λ2 ∈ L(M)` (11)." Remark p. 8: "We note that the result of Proposition 2 applies for any `M ≥ 0`,
even if it is mis-specified." Proof pp. 29–30.

For every data `X ∈ ℝ^{n×p}`, `y ∈ ℝⁿ`, every `λ₀ > 0`, `λ₂ > 0` and every `M ≥ 0`:
(10) if `M ≤ ½√(λ₀/λ₂)` then `V_PR(∞) ≤ V_B(M)`; and (11) if `M ≥ √(λ₀/λ₂)` and `λ₂ ∈ L(M)`
then `V_B(M) ≤ V_PR(∞)`. Here `V_B(M)` and `V_PR(∞)` are the optimal values of the interval
relaxations of B(M) (2) and PR(∞) (3).

**Formalization Note.** `λ₀, λ₂ > 0` (paper.md Reading 1); no hypothesis ties `M` to an optimal
solution of (1) (Reading 2); the values are infima over the relaxations' feasible sets
(Reading 3); `S(λ₂)` is the β-projection of the optimal set (Reading 4); norms are written out
(Reading 5). -/
theorem bigM_vs_perspective_relaxation {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) (lam0 lam2 M : ℝ) (h0 : 0 < lam0) (h2 : 0 < lam2) (hM : 0 ≤ M) :
    (M ≤ 1 / 2 * Real.sqrt (lam0 / lam2) → VPRinf X y lam0 lam2 ≤ VB X y lam0 lam2 M) ∧
    (Real.sqrt (lam0 / lam2) ≤ M → lam2 ∈ Lset X y lam0 M →
      VB X y lam0 lam2 M ≤ VPRinf X y lam0 lam2) := by sorry

end L0BnB.Relax
