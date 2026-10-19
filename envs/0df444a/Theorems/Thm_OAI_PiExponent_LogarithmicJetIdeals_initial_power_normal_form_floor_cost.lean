-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_initial_power_normal_form_floor_cost
-- name    : OAI.PiExponent.LogarithmicJetIdeals.initial_power_normal_form_floor_cost
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T22:24:29.295173+00:00
-- url     : https://prove2.me/theorems/1b21e575-6492-4c22-8a9f-d4edcf29d607
-- title:
--   Floor-cost normal forms from pure-power leading relations
-- statement:
--   Given monic polynomial relations in ideal powers with pairwise coprime pure-power leading monomials, polynomial division yields a representative modulo each ideal power whose support exponents have total floor cost strictly below that power. At power zero the zero polynomial is a valid remainder.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Real.Basic

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.initial_power_normal_form_floor_cost
    {ι : Type*} [Fintype ι] {𝕜 : Type*} [Field 𝕜]
    (I : Ideal (MvPolynomial ι 𝕜))
    (o : MonomialOrder ι)
    (a N : ι → ℕ) (f : ι → MvPolynomial ι 𝕜)
    (ha : ∀ i, 0 < a i) (hN : ∀ i, 0 < N i)
    (hmem : ∀ i, f i ∈ I ^ a i)
    (hlc : ∀ i, o.leadingCoeff (f i) = 1)
    (hdeg : ∀ i, o.degree (f i) = Finsupp.single i (N i)) :
    ∀ k : ℕ, ∀ P : MvPolynomial ι 𝕜,
      ∃ Q : MvPolynomial ι 𝕜,
        (∀ u ∈ Q.support,
          (∑ i, a i * (u i / N i)) < k) ∧
        P - Q ∈ I ^ k := by sorry
