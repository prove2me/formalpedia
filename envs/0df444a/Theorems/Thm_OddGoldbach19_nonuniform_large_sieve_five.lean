-- Prove2me | Theorems.Thm_OddGoldbach19_nonuniform_large_sieve_five
-- name    : OddGoldbach19.nonuniform_large_sieve_five
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T16:42:49.439837+00:00
-- url     : https://prove2.me/theorems/487a4e4a-c44e-4ee7-aa9c-a4df8cbb4504
-- title:
--   Nonuniform large sieve with constant five
-- statement:
--   For any finite family of real frequencies with positive circular gaps delta_r at most1 and the same admissibility condition delta_r <= |theta_r-theta_s+m| for all distinct indices and all integers m, and any finite exponential sum with coefficients a_n indexed by0<=n<N, the sum over frequencies of its squared norm divided by N+5/delta_r is at most the sum of |a_n|^2.
-- source:
--   Derived refinement of the existing Prove2Me weighted Hilbert/large sieve proof chain. Constants derived here, not quoted from literature.  from accepted submission8179bb54-4393-4c46-910f-797a7546eaa2; the original proof is a public Prove2Me Apache2.0 contribution.

import Mathlib
open scoped BigOperators ComplexConjugate

theorem OddGoldbach19.nonuniform_large_sieve_five
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (θ δ : ι → ℝ) (a : ℕ → ℂ)
    (hpos : ∀ r, 0 < δ r) (hunit : ∀ r, δ r ≤ 1)
    (hgap : ∀ r s, r ≠ s → ∀ m : ℤ, δ r ≤ |θ r-θ s+m|) :
    (∑ r, ‖∑ n ∈ Finset.range N,
      a n * Complex.exp (2*(Real.pi : ℂ)*Complex.I*(n : ℂ)*(θ r : ℂ))‖^2 /
      ((N : ℝ)+5/δ r)) ≤ ∑ n ∈ Finset.range N, ‖a n‖^2 := by sorry
