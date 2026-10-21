-- Prove2me | Theorems.Thm_OAI_PiExponent_WeightedDivision_power_monic_relation
-- name    : OAI.PiExponent.WeightedDivision.power_monic_relation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T07:42:45.202983+00:00
-- url     : https://prove2.me/theorems/65538ba9-3aed-48b2-9dad-ab5bbd1e5f8a
-- title:
--   Products of weighted monic relations lift forbidden monomials into ideal powers
-- statement:
--   Over any commutative coefficient ring, if the sum of the natural block quotients of u is at least s, an element G of the s-th relation ideal power makes X^u minus G strictly lower in weight. This single reduction step needs positive block sizes and strict tails, but not positive weights.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

theorem OAI.PiExponent.WeightedDivision.power_monic_relation
    {ι : Type*} {R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (d : ι → ℝ)
    (b : ι → ℕ) (hb : ∀ i, 0 < b i)
    (F : ι → MvPolynomial ι R)
    (hbelow : ∀ i, ∀ v ∈ (MvPolynomial.X i ^ b i - F i).support,
      (∑ j, d j * (v j : ℝ)) < d i * (b i : ℝ))
    (s : ℕ) (u : ι →₀ ℕ)
    (hu : s ≤ ∑ i, u i / b i) :
    ∃ G : MvPolynomial ι R,
      G ∈ (Ideal.span (Set.range F)) ^ s ∧
      ∀ v ∈ (MvPolynomial.monomial u (1 : R) - G).support,
        (∑ i, d i * (v i : ℝ)) < (∑ i, d i * (u i : ℝ)) := by sorry
