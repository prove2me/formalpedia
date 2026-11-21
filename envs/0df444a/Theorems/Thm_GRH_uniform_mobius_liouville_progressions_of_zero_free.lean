-- Prove2me | Theorems.Thm_GRH_uniform_mobius_liouville_progressions_of_zero_free
-- name    : GRH.uniform_mobius_liouville_progressions_of_zero_free
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T01:03:31.162702+00:00
-- url     : https://prove2.me/theorems/1cf04d16-16e9-4416-98eb-409f55fddd07
-- title:
--   Uniform Möbius and Liouville progression bounds from a common Dirichlet zero-free half-plane
-- statement:
--   Let $1/2\le\beta<1$. Assume every Dirichlet $L$-function, for every modulus, is nonzero in $\Re s>\beta$ away from its possible principal pole at $s=1$. Fix $q\ge1$ and a real $\sigma>\beta$. There is a single constant $C=C(q,\sigma,\beta)\ge0$ such that, for every reduced residue class $a\bmod q$ and every integer $N\ge0$, each of the two sums $\left|\sum_{n\le N,\ n\equiv a\pmod q}\mu(n)\right|$ and $\left|\sum_{n\le N,\ n\equiv a\pmod q}\lambda(n)\right|$ is at most $C(N+1)^\sigma$.
-- source:
--   Titchmarsh’s Perron contour estimate, Dirichlet character orthogonality, and the square-divisor expansion of Liouville. Builds on the Prove2Me results of the Masullo specialization concerning logarithmic control (4636708a), Perron transfer (0cfc5f9d), principal pole removal, and the square-divisor progression argument.

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open ArithmeticFunction Finset

theorem GRH.uniform_mobius_liouville_progressions_of_zero_free (β : ℝ) (hβ : 1/2 ≤ β) (hβ₁ : β < 1)
    (hzero : ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (s : ℂ),
      β < s.re → ¬ (χ = 1 ∧ s = 1) → χ.LFunction s ≠ 0)
    (q : ℕ) [NeZero q] (σ : ℝ) (hσ : β < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ZMod q, IsUnit a → ∀ N : ℕ,
      |∑ k ∈ range (N+1), if (k : ZMod q) = a then (moebius k : ℝ) else 0| ≤ C*((N:ℝ)+1)^σ ∧
      |∑ k ∈ range (N+1), if (k : ZMod q) = a then (liouville k : ℝ) else 0| ≤ C*((N:ℝ)+1)^σ := by sorry
