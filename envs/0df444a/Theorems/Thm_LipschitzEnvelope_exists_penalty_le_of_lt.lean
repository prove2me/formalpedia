-- Prove2me | Theorems.Thm_LipschitzEnvelope_exists_penalty_le_of_lt
-- name    : LipschitzEnvelope.exists_penalty_le_of_lt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T07:51:29.767199+00:00
-- url     : https://prove2.me/theorems/e50458c3-f8d4-4a3e-a8d3-30270d5fe0cd
-- title:
--   A penalty weight that pushes the Lipschitz envelope below a given level
-- statement:
--   Let $E$ be a real normed space, $\Xi \subseteq E$, $L : E \to \overline{\mathbb{R}}$, and fix
--   $\hat x \in E$. For a weight $\lambda \in \mathbb{R}$ consider the penalized supremum
--
--   $$
--   e_\lambda = \sup_{x \in \Xi} \bigl( L(x) - \lambda \|x - \hat x\| \bigr) .
--   $$
--
--   Suppose $L$ is upper semicontinuous at $\hat x$, admits an affine majorant
--   $L(x) \le C + A\|x - \hat x\|$ on $\Xi$ for some $C, A \in \mathbb{R}$, and satisfies
--   $L(\hat x) < r$ for a given $r \in \mathbb{R}$. Then some weight already brings the whole
--   supremum below $r$:
--
--   $$
--   \exists\, \lambda \ge 0 \ \text{ such that } \ e_\lambda \le r .
--   $$
--
--   $e_\lambda$ is the Pasch–Hausdorff (Lipschitz) regularization of $L$: the smallest
--   $\lambda$-Lipschitz majorant seen from $\hat x$. Charging a price per unit of distance
--   suppresses whatever $L$ does far from $\hat x$, and the statement says the price needed is
--   finite as soon as $L$ is affinely dominated and upper semicontinuous at the base point. It is
--   the quantitative half of the convergence statement, and the form an argument uses when it needs
--   one concrete weight rather than a limit.
-- source:
--   P. Mohajerin Esfahani and D. Kuhn, Data-driven distributionally robust optimization using the Wasserstein metric: performance guarantees and tractable reformulations, Mathematical Programming 171 (2018), 115-166. Carved from https://prove2.me/submissions/9d9b1da1-23a8-4b1d-b0ad-3d6a8366c2eb, lines 819-854, the accepted proof of WassDDRO.Extremal.theorem_4_4. The same statement is proved inline in https://prove2.me/submissions/6e4986f7-2b7e-4a8d-97e1-f19f9c2537ac as well, the accepted proof of WassDDRO.Reduction.theorem_4_2, so two missions were each carrying their own derivation of it

import Mathlib

set_option autoImplicit false
open Filter Topology Set

theorem LipschitzEnvelope.exists_penalty_le_of_lt {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (L : E → EReal) (xhat : E) (C A r : ℝ)
    (husc : UpperSemicontinuousAt L xhat)
    (hupper : ∀ x ∈ Ξ, L x ≤ ((C+A*‖x-xhat‖ : ℝ) : EReal))
    (hr : L xhat < (r : EReal)) :
    ∃ lam : ℝ, 0 ≤ lam ∧
      (⨆ x ∈ Ξ, L x-((lam*‖x-xhat‖ : ℝ) : EReal)) ≤ (r : EReal) := by sorry
