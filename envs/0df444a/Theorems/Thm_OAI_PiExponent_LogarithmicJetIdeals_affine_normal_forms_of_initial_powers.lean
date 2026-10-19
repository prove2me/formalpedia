-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_affine_normal_forms_of_initial_powers
-- name    : OAI.PiExponent.LogarithmicJetIdeals.affine_normal_forms_of_initial_powers
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T02:47:09.153706+00:00
-- url     : https://prove2.me/theorems/2a58ce66-2693-4ccf-b4cb-15e299011f99
-- title:
--   Affine weighted normal forms from finite pure leading-power certificates
-- statement:
--   Over any field, monic relations in ideal powers with pure-power leading monomials and compatible weight budgets give representatives modulo every ideal power, with an explicit uniform affine bound. Division by products proves the assertion, including the zeroth power.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Real.Basic

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.affine_normal_forms_of_initial_powers
    {ι : Type*} [Fintype ι] {𝕜 : Type*} [Field 𝕜]
    (I : Ideal (MvPolynomial ι 𝕜))
    (w : ι → ℝ) (ρ : ℝ) (o : MonomialOrder ι)
    (a N : ι → ℕ) (f : ι → MvPolynomial ι 𝕜)
    (hw : ∀ i, 0 ≤ w i) (hρ : 0 ≤ ρ)
    (ha : ∀ i, 0 < a i) (hN : ∀ i, 0 < N i)
    (hmem : ∀ i, f i ∈ I ^ a i)
    (hlc : ∀ i, o.leadingCoeff (f i) = 1)
    (hdeg : ∀ i, o.degree (f i) = Finsupp.single i (N i))
    (hbudget : ∀ i, (N i : ℝ) * w i ≤ (a i : ℝ) * ρ) :
    ∀ k : ℕ, ∀ P : MvPolynomial ι 𝕜,
      ∃ Q : MvPolynomial ι 𝕜,
        (∀ u ∈ Q.support,
          (∑ i, w i * (u i : ℝ)) ≤
            (k : ℝ) * ρ + ∑ i, w i * ((N i - 1 : ℕ) : ℝ)) ∧
        P - Q ∈ I ^ k := by sorry
