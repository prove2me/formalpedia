-- Prove2me | Theorems.Thm_MvPolynomial_eq_of_forall_eval_rpow_eq
-- name    : MvPolynomial.eq_of_forall_eval_rpow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/c7889689-1e74-5e0a-b2b0-39250aab3bf9
-- title:
--   Polynomial identity on S × {N^u} holds identically
-- statement:
--   Let $N$ be a natural number with $1 < N$, let $u_0$ be a real number, and let $S \subseteq \mathbb{C}$ be an infinite set. Let $P, Q$ be polynomials in two variables over $\mathbb{C}$, i.e. elements of `MvPolynomial (Fin 2) ℂ`. Suppose that for every $x \in S$ and every real $u > u_0$ the two polynomials agree at the point whose first coordinate is $x$ and whose second coordinate is the complex number obtained from the real power $N^{u}$ (real `rpow`), that is, $P(x, N^{u}) = Q(x, N^{u})$, evaluation being taken at the vector `![x, ((N : ℝ) ^ u : ℝ)]`. The conclusion is the equality $P = Q$ of polynomials, not merely of the functions they define. The hypothesis $1 < N$ enters only through the strict monotonicity, hence injectivity, of $u \mapsto N^{u}$ on $\mathbb{R}$, which makes the set of second coordinates infinite.
--
--   This is the elementary principle that a polynomial identity in two variables over an integral domain valid on a product of two infinite sets is an identity of polynomials, specialised to the second factor $\{N^{u} : u > u_0\}$. It is used as the resummation step in the local Rankin–Selberg computations of the cubic-induction part of the Langlands–Tunnell input, where an identity in $N^{1/2-s}$ and $N^{u}$ known for large $u$ is propagated to all values, in particular to $u = 0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_eq_of_forall_eval_rpow_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem MvPolynomial.eq_of_forall_eval_rpow_eq (N : ℕ) (hN : 1 < N) (u₀ : ℝ) (S : Set ℂ)
    (hS : S.Infinite) (P Q : MvPolynomial (Fin 2) ℂ)
    (h : ∀ x ∈ S, ∀ u : ℝ, u₀ < u →
      MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] P =
        MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] Q) :
    P = Q := by sorry
