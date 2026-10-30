-- Prove2me | Theorems.Thm_L0BnB_Relax_omega_value_M_infty
-- name    : L0BnB.Relax.omega_value_M_infty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:48:03.313927+00:00
-- url     : https://prove2.me/theorems/6448323b-c614-4fca-bcc8-d8078c15b70a
-- title:
--   Per-coordinate value of the PR(∞) relaxation (proof of Theorem 1, (36), with $M=\infty$)
-- statement:
--   Let $\lambda_0,\lambda_2>0$ and $b\in\mathbb R$. The one-dimensional problem
--
--   $$\omega(b)=\min\{\lambda_0z+\lambda_2s\ :\ 0\le z\le1,\ s\ge0,\ b^2\le sz\}$$
--
--   has a minimum, and
--
--   $$\omega(b)=\psi_1(b;\lambda_0,\lambda_2)=2\lambda_0\,\mathcal B\bigl(b\sqrt{\lambda_2/\lambda_0}\bigr).$$
--
--   This is the computation in the proof of Theorem 1 at $M=\infty$, where the Big-M constraint (35c) is absent. Summed over coordinates it turns the $(\beta,z,s)$ relaxation of PR$(\infty)$ into the $\beta$-space problem (6).
--
--   Differences from the source:
--   - encoding: λ0, λ2 regularization parameters "specified by the practitioner" (p. 2), no sign stated → hypotheses 0 < lam0 and 0 < lam2; reason: paper.md Reading 1: √(λ0/λ2), √(λ2/λ0) and ψ1 are undefined otherwise, and L(M) ⊆ (0, ∞) by (9); only undefined cases are excluded
--   - reading: ω(βi; λ0, λ2, M) with constraints (35b), (35c), (35d), computed assuming √(λ0/λ2) ≤ M → M = ∞: constraint (35c) dropped, the assumption √(λ0/λ2) ≤ M holds; reason: the paper applies this computation with M = ∞ to obtain (6) (pp. 7 and 29); the finite-M Theorem 1 is not a milestone of this mission
--   - encoding: "min" in ω(βi; λ0, λ2, M) := min_{si,zi}(λ0zi + λ2si) → IsLeast of the set of values (attained and a lower bound); reason: IsLeast is exactly the statement that the minimum exists and equals the value
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, proof of Theorem 1, (35)–(36), p. 28, with M = ∞ (p. 7: "(6) can also be obtained from Theorem 1 (with M = ∞)")

import Mathlib
import Definitions.Def_L0BnB_Relax_psi1

namespace L0BnB.Relax

/-- **Per-coordinate value of the PR(∞) relaxation** (proof of Theorem 1, (36), with `M = ∞`).
Hazimeh, Mazumder, Saab, *Sparse Regression at Scale: Branch-and-Bound rooted in First-Order
Optimization*, arXiv:2004.06152v2, proof of Theorem 1, p. 28: "Let `ω(βi; λ0, λ2, M) := min_{si,zi}(λ0zi + λ2si)` s.t.
(35b), (35c), (35d)." … "Plugging `s∗i` into (36) leads to `ω(βi; λ0, λ2, M) =
2λ0B(βi√(λ2/λ0))`, assuming `√(λ0/λ2) ≤ M`." With `M = ∞` (p. 7: "(6) can also be obtained
from Theorem 1 (with M = ∞)"), the constraint (35c) is absent and the assumption holds.

For `λ₀, λ₂ > 0` and every `b ∈ ℝ`, the minimum of `λ₀ z + λ₂ s` over
`{(z, s) : 0 ≤ z ≤ 1, 0 ≤ s, b² ≤ s z}` exists and equals `ψ₁(b; λ₀, λ₂)`.

**Formalization Note.** "min" is `IsLeast` of the set of objective values: the value
`ψ₁(b; λ₀, λ₂)` is attained by a feasible `(z, s)` and is a lower bound of all of them. The corner
`b = 0`, `z = 0` is included (value `0`). -/
theorem omega_value_M_infty (lam0 lam2 : ℝ) (h0 : 0 < lam0) (h2 : 0 < lam2) (b : ℝ) :
    IsLeast {v | ∃ z s : ℝ, 0 ≤ z ∧ z ≤ 1 ∧ 0 ≤ s ∧ b ^ 2 ≤ s * z ∧ lam0 * z + lam2 * s = v}
      (psi1 lam0 lam2 b) := by sorry

end L0BnB.Relax
