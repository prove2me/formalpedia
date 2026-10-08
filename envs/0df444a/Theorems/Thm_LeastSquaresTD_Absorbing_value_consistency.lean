-- Prove2me | Theorems.Thm_LeastSquaresTD_Absorbing_value_consistency
-- name    : LeastSquaresTD.Absorbing.value_consistency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:02:46.804228+00:00
-- url     : https://prove2.me/theorems/407730be-7794-4d96-888f-bc5bd0051ac5
-- title:
--   Equation (12) — finite true value parameter and consistency
-- statement:
--   For an absorbing finite Markov chain with rewards zero between absorbing states, take $0\le\gamma\le1$. Suppose the non-absorbing feature vectors are linearly independent, absorbing feature vectors vanish, and the feature dimension is the number of non-absorbing states. Then the expected-return series converges at every state, and there is a parameter $\theta^*$ representing its value function such that
--
--   $$
--   V(x)=\phi_x^\top\theta^*\quad(x\in X),\qquad
--   \bar r=(I-\gamma P)\Phi\theta^*.
--   $$
--
--   This supplies the finite true parameter and the consistency relation used to identify the LS TD limit with it.
--
--   **Formalization Note** At $\gamma=1$, summability follows from absorption and the zero-reward condition; it is stated explicitly because a divergent real `tsum` would otherwise have a default value. The parameter is existential, not defined by the limiting LS TD matrix.
-- source:
--   Bradtke and Barto, Linear Least-Squares Algorithms for Temporal Difference Learning, Machine Learning 22 (1996), https://doi.org/10.1023/A:1018056104778, p. 44, Proof of Theorem 1, Eq. (12) and following sentence; p. 41, Eq. (9)

import Definitions.Def_LeastSquaresTD_Absorbing_Estimator

namespace LeastSquaresTD.Absorbing

variable {m : ℕ}

/-- Proof of Theorem 1, p. 44, Eq. (12), together with the paper's
claim that `θ*` is finite. The value function is the return series, so
summability at `γ = 1` remains part of this conclusion. -/
theorem value_consistency
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (C : Chain X) (R : X → X → ℝ) (φ : X → Fin m → ℝ) (γ : ℝ)
    (habs : C.IsAbsorbing) (hRabs : ∀ x y, C.P x x = 1 → C.P y y = 1 → R x y = 0)
    (hm : m = Fintype.card C.Nonabsorbing)
    (hli : LinearIndependent ℝ (fun x : C.Nonabsorbing => φ x.val))
    (hφabs : ∀ x, C.P x x = 1 → φ x = 0)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ∃ θstar : Fin m → ℝ,
      (∀ x, Summable (fun k : ℕ => γ ^ k *
        (Matrix.mulVec (C.P ^ k) (C.rbar R)) x)) ∧
      (∀ x, C.value R γ x = ∑ i, φ x i * θstar i) ∧
      C.rbar R = Matrix.mulVec (1 - γ • C.P)
        (Matrix.mulVec (Matrix.of φ) θstar) := by sorry

end LeastSquaresTD.Absorbing
