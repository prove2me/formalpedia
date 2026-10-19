-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_extract_pure_leading_relations
-- name    : OAI.PiExponent.LogarithmicJetIdeals.extract_pure_leading_relations
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T23:03:51.04398+00:00
-- url     : https://prove2.me/theorems/4d95e502-bcd2-48dd-afe6-c5bb6d8138e1
-- title:
--   Extract monic pure-leading relations from bounded representatives
-- statement:
--   Using the bounded representative of each pure-power monomial, form its difference from that representative. The strict weight and order bounds ensure the pure power is the unique leading term, with coefficient one, while the difference belongs to the ideal.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Complex.Basic

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.extract_pure_leading_relations (m : ℕ) (w : Fin (m + 1) → ℝ) (D : ℝ) (I : Ideal (MvPolynomial (Fin (m + 1)) ℂ)) (N : Fin (m + 1) → ℕ) (o : MonomialOrder (Fin (m + 1))) (hN : ∀ i, D < (N i : ℝ) * w i) (ho : ∀ i b, (∑ j, w j * (b j : ℝ) ≤ D) → o.toSyn b < o.toSyn (Finsupp.single i (N i))) (hrep : ∀ P : MvPolynomial (Fin (m + 1)) ℂ, ∃ Q : MvPolynomial (Fin (m + 1)) ℂ, P - Q ∈ I ∧ ∀ b ∈ Q.support, ∑ i, w i * (b i : ℝ) ≤ D) : ∃ f : Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℂ, (∀ i, f i ∈ I) ∧ (∀ i, o.leadingCoeff (f i) = 1) ∧ (∀ i, o.degree (f i) = Finsupp.single i (N i)) := by sorry
