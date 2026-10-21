-- Prove2me | Theorems.Thm_OAI_PiExponent_weighted_monic_staircase_remainder
-- name    : OAI.PiExponent.weighted_monic_staircase_remainder
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T21:58:29.381911+00:00
-- url     : https://prove2.me/theorems/c4043302-4cd1-49bd-b964-0b42f50c2ccc
-- title:
--   Weighted monic division gives staircase remainders modulo ideal powers
-- statement:
--   For finitely many variables with positive real weights, coordinate relations with pure-power leading monomials and strictly lower-weight tails give representatives modulo every power of their generated ideal. Every supported remainder exponent has sum of coordinatewise block quotients strictly below that power.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

theorem OAI.PiExponent.weighted_monic_staircase_remainder
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (hd : ∀ i, 0 < d i)
    (b : ι → ℕ) (hb : ∀ i, 0 < b i)
    (F : ι → MvPolynomial ι ℂ)
    (hbelow : ∀ i, ∀ u ∈ (MvPolynomial.X i ^ b i - F i).support,
      (∑ j, d j * (u j : ℝ)) < d i * (b i : ℝ))
    (s : ℕ) (P : MvPolynomial ι ℂ) :
    ∃ Q : MvPolynomial ι ℂ,
      P - Q ∈ (Ideal.span (Set.range F)) ^ s ∧
      ∀ u ∈ Q.support, (∑ i, u i / b i) < s := by sorry
