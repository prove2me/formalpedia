-- Prove2me | Theorems.Thm_LeastSquaresTD_Absorbing_limit_matrix_invertible
-- name    : LeastSquaresTD.Absorbing.limit_matrix_invertible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:02:16.12322+00:00
-- url     : https://prove2.me/theorems/8601bcbb-6884-4423-94e9-f4733679aa20
-- title:
--   Proof of Theorem 1 — invertibility of the LS TD limit matrix
-- statement:
--   Let $P$ be an absorbing finite-state transition matrix, with $0\le\gamma\le1$. Suppose the feature vectors of non-absorbing states are linearly independent, the feature vectors of absorbing states are zero, and their dimension equals the number of non-absorbing states. Let $\pi_x>0$ on every non-absorbing state. Then
--
--   $$
--   \Phi^\top\Pi(I-\gamma P)\Phi\quad\text{is invertible},\qquad \Pi=\operatorname{diag}(\pi).
--   $$
--
--   This is the rank conclusion in the proof of Theorem 1 and ensures that Lemma 5's limiting estimate is well defined.
--
--   **Formalization Note** The paper's actual visit weights vanish on absorbing states. The statement allows arbitrary weights there because the corresponding feature rows vanish; this is the slight generalization noted in the chapter brief.
-- source:
--   Bradtke and Barto, Linear Least-Squares Algorithms for Temporal Difference Learning, Machine Learning 22 (1996), https://doi.org/10.1023/A:1018056104778, p. 44, Proof of Theorem 1, rank argument for A, B, C

import Definitions.Def_LeastSquaresTD_Absorbing_Estimator

namespace LeastSquaresTD.Absorbing

variable {m : ℕ}

/-- Proof of Theorem 1, p. 44: `ΦᵀΠ(I - γP)Φ` has full rank. The proof
uses `ΦᵀΠ(I - γP)Φ = AᵀBCA`. Values of `π` on absorbing states do not
matter because the corresponding feature rows vanish. -/
theorem limit_matrix_invertible
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (C : Chain X) (φ : X → Fin m → ℝ) (γ : ℝ) (π : X → ℝ)
    (habs : C.IsAbsorbing) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hm : m = Fintype.card C.Nonabsorbing)
    (hli : LinearIndependent ℝ (fun x : C.Nonabsorbing => φ x.val))
    (hφabs : ∀ x, C.P x x = 1 → φ x = 0)
    (hπ : ∀ x : C.Nonabsorbing, 0 < π x.val) :
    IsUnit (limitMatrix C φ γ π) := by sorry

end LeastSquaresTD.Absorbing
