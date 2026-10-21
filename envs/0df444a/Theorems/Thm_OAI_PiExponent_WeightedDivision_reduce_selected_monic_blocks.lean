-- Prove2me | Theorems.Thm_OAI_PiExponent_WeightedDivision_reduce_selected_monic_blocks
-- name    : OAI.PiExponent.WeightedDivision.reduce_selected_monic_blocks
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:26:37.826482+00:00
-- url     : https://prove2.me/theorems/375ee187-9e62-430d-9714-e4d27123cc9e
-- title:
--   Replace selected monic blocks by lower-weight relations
-- statement:
--   Given block multiplicities fitting in the exponent vector and totaling $s$, replace those monic blocks by their lower-weight relations to obtain an element of the $s$-th ideal power whose difference from the original monomial has strictly lower-weight support.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

theorem OAI.PiExponent.WeightedDivision.reduce_selected_monic_blocks
    {ι : Type*} {R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (d : ι → ℝ)
    (b : ι → ℕ) (hb : ∀ i, 0 < b i)
    (F : ι → MvPolynomial ι R)
    (hbelow : ∀ i, ∀ v ∈ (MvPolynomial.X i ^ b i - F i).support,
      (∑ j, d j * (v j : ℝ)) < d i * (b i : ℝ))
    (s : ℕ) (u : ι →₀ ℕ) (k : ι → ℕ)
    (hkdiv : ∀ i, k i * b i ≤ u i)
    (hksum : ∑ i, k i = s) :
    ∃ G : MvPolynomial ι R,
      G ∈ (Ideal.span (Set.range F)) ^ s ∧
      ∀ v ∈ (MvPolynomial.monomial u (1 : R) - G).support,
        (∑ i, d i * (v i : ℝ)) < (∑ i, d i * (u i : ℝ)) := by sorry
