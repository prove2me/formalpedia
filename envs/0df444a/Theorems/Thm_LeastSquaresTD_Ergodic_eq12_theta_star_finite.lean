-- Prove2me | Theorems.Thm_LeastSquaresTD_Ergodic_eq12_theta_star_finite
-- name    : LeastSquaresTD.Ergodic.eq12_theta_star_finite
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:18:19.703988+00:00
-- url     : https://prove2.me/theorems/041d0963-4335-45b1-ac35-846cdf7ecf82
-- title:
--   Eq. (12), p. 44, and p. 45 — θ* is finite and r̄ = (I − γP)Φθ*
-- statement:
--   Let $P$ be the transition matrix of a Markov chain on a finite nonempty state set $X$, with rewards $R$ and expected rewards $\bar r$. Let $\{\phi_x\mid x\in X\}\subset\mathbb R^m$ be linearly independent with $m=|X|$, $\Phi$ the matrix with rows $\phi_x$, and $0<\gamma<1$. Then the value series $V(x)=\sum_{k\ge0}\gamma^k(P^k\bar r)(x)$ converges at every state, and there is a parameter vector $\theta^*\in\mathbb R^m$ with $V(x)=\phi_x'\theta^*$ for every $x\in X$ which satisfies the consistency condition in matrix form
--   $$\bar r=(I-\gamma P)\,\Phi\,\theta^* .\tag{12}$$
--
--   Equation (12) is what turns Lemma 5's limit into $\theta^*$ at the end of the proof of Theorem 2.
--
--   **Formalization Note** "θ* is finite" is formalized as the existence of a real vector $\theta^*$ representing $V$, together with the convergence of the value series (Lean's infinite sum is $0$ for a divergent series). Ergodicity is not needed for this statement and is not assumed.
-- source:
--   Bradtke and Barto, Linear Least-Squares Algorithms for Temporal Difference Learning, Machine Learning 22 (1996), p. 44, Eq. (12); p. 45, Proof of Theorem 2 ('Condition (3) together with Equation (12) imply that θ* is finite'); p. 41, Eq. (9)

import Mathlib
import Definitions.Def_LeastSquaresTD_Ergodic_Chain
import Definitions.Def_LeastSquaresTD_Ergodic_LSTD
open MeasureTheory Matrix Filter Topology

namespace LeastSquaresTD.Ergodic

/-- Eq. (12), p. 44, and "θ* is finite", p. 45: for a finite chain, linearly independent features
of dimension `m = |X|` and `0 < γ < 1`, the value series converges at every state, there is a
parameter `θ*` with `V(x) = φₓ'θ*` for all `x`, and it satisfies `r̄ = (I − γP)Φθ*`. -/
theorem eq12_theta_star_finite {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (C : Chain X) (R : X → X → ℝ) {m : ℕ} (φ : X → Fin m → ℝ) (hφ : LinearIndependent ℝ φ)
    (hm : m = Fintype.card X) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ θstar : Fin m → ℝ,
      (∀ x, Summable (fun k : ℕ => γ ^ k * ((C.P ^ k) *ᵥ C.rbar R) x)) ∧
      (∀ x, C.value R γ x = φ x ⬝ᵥ θstar) ∧
      C.rbar R = (1 - γ • C.P) *ᵥ (featureMatrix φ *ᵥ θstar) := by sorry

end LeastSquaresTD.Ergodic
