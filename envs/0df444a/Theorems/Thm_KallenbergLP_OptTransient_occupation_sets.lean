-- Prove2me | Theorems.Thm_KallenbergLP_OptTransient_occupation_sets
-- name    : KallenbergLP.OptTransient.occupation_sets
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:52:57.031995+00:00
-- url     : https://prove2.me/theorems/2488e113-f951-4167-b5f4-2b22d621cb02
-- title:
--   Theorem 3.3.4 — occupation sets of the four policy classes
-- statement:
--   Assume, as throughout Section 3.3, that a transient policy exists. Let $\beta$ be a strictly positive initial distribution. Write $K(D),K(S),K(M),K$ for occupation vectors from transient pure stationary, stationary, Markov, and arbitrary history-dependent randomized policies, respectively; let $P$ be the feasible set of (3.3.7). Then
--
--   $$
--   \overline{K(D)}\subset K(S)=K(M)=K=P.
--   $$
--
--   The bar denotes the closed convex hull. Since the state and action sets are finite, $K(D)$ is finite and its convex hull is closed. This theorem shows that the LP feasible set captures every transient policy class while the pure stationary class need not fill it.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 55, Theorem 3.3.4; p. 9, Definition 1.2.1(i) for the bar notation; https://ir.cwi.nl/pub/13008

import Mathlib
import Definitions.Def_KallenbergLP_OptTransient_LinearProgram

namespace KallenbergLP.OptTransient

/-- Theorem 3.3.4, printed p. 55. The bar denotes closed convex hull; K(D) is finite. -/
theorem occupation_sets {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ)
    (hex : ∃ R : Policy n α, IsPolicy m R ∧ IsTransient m R)
    (hβ : ∀ i, 0 < β i) (hβsum : ∑ i, β i = 1) :
    convexHull ℝ (KPure m β) ⊆ KStationary m β ∧
    KStationary m β = KMarkov m β ∧
    KMarkov m β = K m β ∧
    K m β = feasibleSet m β := by sorry

end KallenbergLP.OptTransient
