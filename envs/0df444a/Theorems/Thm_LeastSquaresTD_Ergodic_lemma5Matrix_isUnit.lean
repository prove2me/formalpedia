-- Prove2me | Theorems.Thm_LeastSquaresTD_Ergodic_lemma5Matrix_isUnit
-- name    : LeastSquaresTD.Ergodic.lemma5Matrix_isUnit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:18:06.080035+00:00
-- url     : https://prove2.me/theorems/2771d2c7-2a3d-4177-993f-a9057a7aa2d0
-- title:
--   Proof of Theorem 2, p. 45 — π > 0 and Φ'Π(I − γP)Φ is invertible
-- statement:
--   Let $P$ be the transition matrix of an ergodic (irreducible) Markov chain on a finite nonempty state set $X$, and let $\pi$ be an invariant distribution of $P$, with $\Pi=\operatorname{diag}(\pi)$. Let $\{\phi_x\mid x\in X\}\subset\mathbb R^m$ be linearly independent feature vectors with $m=|X|$, and let $\Phi$ be the matrix whose $x$-th row is $\phi_x$. If $0<\gamma<1$, then $\pi_x>0$ for every $x\in X$ and the $m\times m$ matrix
--   $$\Phi'\,\Pi\,(I-\gamma P)\,\Phi$$
--   is invertible.
--
--   This is condition (4) of Lemma 5 in the setting of Theorem 2; the paper derives it from the invertibility of $\Pi$, $I-\gamma P$ and $\Phi$.
--
--   **Formalization Note** "Ergodic" is read as irreducible. Condition (2) of Theorem 2, "each $\phi_x$ is of dimension $N=|X|$", is the hypothesis $m=|X|$.
-- source:
--   Bradtke and Barto, Linear Least-Squares Algorithms for Temporal Difference Learning, Machine Learning 22 (1996), p. 45, Proof of Theorem 2

import Mathlib
import Definitions.Def_LeastSquaresTD_Ergodic_Chain
import Definitions.Def_LeastSquaresTD_Ergodic_LSTD
open MeasureTheory Matrix Filter Topology

namespace LeastSquaresTD.Ergodic

/-- Proof of Theorem 2, p. 45: for an ergodic chain with invariant distribution `π`, linearly
independent features `φₓ` of dimension `m = |X|` and `0 < γ < 1`, every `πₓ` is positive and
the matrix `Φ'Π(I − γP)Φ` of Lemma 5 is invertible. -/
theorem lemma5Matrix_isUnit {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (C : Chain X) (hC : C.IsErgodic) (π : X → ℝ) (hπ : C.IsStationary π)
    {m : ℕ} (φ : X → Fin m → ℝ) (hφ : LinearIndependent ℝ φ) (hm : m = Fintype.card X)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    (∀ x, 0 < π x) ∧ IsUnit (lemma5Matrix C φ π γ) := by sorry

end LeastSquaresTD.Ergodic
