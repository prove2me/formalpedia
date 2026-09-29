-- Prove2me | Theorems.Thm_JewellMRP_Discounted_diag_inv_ge_one
-- name    : JewellMRP.Discounted.diag_inv_ge_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:01:09.52426+00:00
-- url     : https://prove2.me/theorems/e8162f9c-e309-4acb-aede-fb248d5f5841
-- title:
--   p. 946 — the diagonal elements of $[I-\tilde q(\alpha)]^{-1}$ are at least one
-- statement:
--   Let a Markov-renewal program be given, let $\alpha > 0$ and let $d$ be a stationary policy. Let $\tilde q(\alpha)$ be the $S \times S$ matrix with entries $\tilde q_{ij}(\alpha) = p^{d(i)}_{ij}\,\tilde f^{d(i)}_{ij}(\alpha)$. Then $I - \tilde q(\alpha)$ is invertible and
--   $$
--   \big([I - \tilde q(\alpha)]^{-1}\big)_{ii} \ge 1 \qquad \text{for every } i \in S .
--   $$
--
--   The paper invokes this as "the additional observation" required for the proof of Claim (b): it turns a strict improvement of the test quantity in one state into a strict increase of that state's return.
--
--   **Formalization Note** Invertibility is stated explicitly, so that the inverse is the genuine inverse and not Mathlib's junk value for singular matrices. The matrix is that of the policy $d$ ("the dependence upon the policy has been suppressed" in the paper).
-- source:
--   Jewell, Markov-Renewal Programming. I: Formulation, Finite Return Models, Operations Research 11(6), 1963, p. 946, Discounted Models with Infinite Step or Time Horizons (observation for the proof of Claim (b))

import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP

namespace JewellMRP.Discounted

/-- p. 946: for `α > 0` and a stationary policy `d`, the matrix `I - q̃(α)` of `d` is invertible
and every diagonal element of `[I - q̃(α)]⁻¹` is at least one. -/
theorem diag_inv_ge_one {S A : Type*} [Fintype S] [DecidableEq S] (M : MRP S A) {α : ℝ}
    (hα : 0 < α) (d : S → A) :
    IsUnit (1 - Matrix.of (fun i j => qtilde M α (d i) i j)) ∧
      ∀ i, 1 ≤ (1 - Matrix.of (fun i j => qtilde M α (d i) i j))⁻¹ i i := by sorry

end JewellMRP.Discounted
