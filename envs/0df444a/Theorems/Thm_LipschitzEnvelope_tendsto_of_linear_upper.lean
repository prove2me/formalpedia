-- Prove2me | Theorems.Thm_LipschitzEnvelope_tendsto_of_linear_upper
-- name    : LipschitzEnvelope.tendsto_of_linear_upper
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T07:51:30.372895+00:00
-- url     : https://prove2.me/theorems/e375c680-59b4-4cb2-b822-830b40315a34
-- title:
--   The Lipschitz envelope converges to the base value as the penalty grows
-- statement:
--   Let $E$ be a real normed space, $\Xi \subseteq E$ with $\hat x \in \Xi$, and
--   $L : E \to \overline{\mathbb{R}}$ upper semicontinuous at $\hat x$ and affinely dominated on
--   $\Xi$: $L(x) \le C + A\|x - \hat x\|$ for some $C, A \in \mathbb{R}$. Then the penalized
--   supremum converges to the value at the base point:
--
--   $$
--   \sup_{x \in \Xi} \bigl( L(x) - \lambda\|x - \hat x\| \bigr) \ \longrightarrow \ L(\hat x)
--   \qquad \text{as } \lambda \to \infty .
--   $$
--
--   This is the consistency of Lipschitz regularization: as the price per unit of distance grows
--   without bound, the worst case over $\Xi$ collapses onto the base point. One inequality is
--   immediate, since $\hat x \in \Xi$ contributes $L(\hat x)$ to every supremum; the content is the
--   other one, and it is exactly where upper semicontinuity at $\hat x$ and the affine majorant are
--   needed. In distributionally robust optimization the limit says that the worst-case loss over a
--   Wasserstein ball shrinks to the nominal loss as the transport budget vanishes, and the same
--   statement serves anywhere a penalized worst case has to be identified with a pointwise value.
--
--   **Formalization Note.** The supremum is taken in `EReal`, so no finiteness has to be assumed and
--   the limit is stated in the order topology of `EReal`. The penalty is linear in the norm, not
--   quadratic: this is the Pasch–Hausdorff envelope and not the Moreau envelope, and the limit is
--   taken as the weight grows rather than as it vanishes.
-- source:
--   P. Mohajerin Esfahani and D. Kuhn, Data-driven distributionally robust optimization using the Wasserstein metric: performance guarantees and tractable reformulations, Mathematical Programming 171 (2018), 115-166. Carved from https://prove2.me/submissions/9d9b1da1-23a8-4b1d-b0ad-3d6a8366c2eb, lines 855-928, the accepted proof of WassDDRO.Extremal.theorem_4_4. The same statement is proved inline in https://prove2.me/submissions/6e4986f7-2b7e-4a8d-97e1-f19f9c2537ac as well, the accepted proof of WassDDRO.Reduction.theorem_4_2, so two missions were each carrying their own derivation of it

import Mathlib

set_option autoImplicit false
open Filter Topology Set

theorem LipschitzEnvelope.tendsto_of_linear_upper {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (L : E → EReal) (xhat : E) (hxhat : xhat ∈ Ξ) (C A : ℝ)
    (husc : UpperSemicontinuousAt L xhat)
    (hupper : ∀ x ∈ Ξ, L x ≤ ((C+A*‖x-xhat‖ : ℝ) : EReal)) :
    Tendsto (fun lam : ℝ => ⨆ x ∈ Ξ, L x-((lam*‖x-xhat‖ : ℝ) : EReal))
      atTop (𝓝 (L xhat)) := by sorry
