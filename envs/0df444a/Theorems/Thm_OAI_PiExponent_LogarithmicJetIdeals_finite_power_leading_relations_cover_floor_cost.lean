-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_power_leading_relations_cover_floor_cost
-- name    : OAI.PiExponent.LogarithmicJetIdeals.finite_power_leading_relations_cover_floor_cost
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T22:33:01.962079+00:00
-- url     : https://prove2.me/theorems/672e04fc-1669-45b8-9515-a45ec1fc0c71
-- title:
--   Finite power relations cover exponents above floor cost
-- statement:
--   For each power threshold, there is a finite family of monic products of the given relations, all in that ideal power, whose leading exponents divide every monomial whose floor cost reaches the threshold.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Real.Basic

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.finite_power_leading_relations_cover_floor_cost
    {ι : Type*} [Fintype ι] {𝕜 : Type*} [Field 𝕜]
    (I : Ideal (MvPolynomial ι 𝕜))
    (o : MonomialOrder ι)
    (a N : ι → ℕ) (f : ι → MvPolynomial ι 𝕜)
    (ha : ∀ i, 0 < a i) (hN : ∀ i, 0 < N i)
    (hmem : ∀ i, f i ∈ I ^ a i)
    (hlc : ∀ i, o.leadingCoeff (f i) = 1)
    (hdeg : ∀ i, o.degree (f i) = Finsupp.single i (N i))
    (k : ℕ) :
    ∃ S : Finset (MvPolynomial ι 𝕜),
      (∀ g ∈ S, g ∈ I ^ k ∧ o.leadingCoeff g = 1) ∧
      (∀ u : ι → ℕ,
        k ≤ (∑ i, a i * (u i / N i)) →
          ∃ g ∈ S, o.degree g ≤ u) := by sorry
