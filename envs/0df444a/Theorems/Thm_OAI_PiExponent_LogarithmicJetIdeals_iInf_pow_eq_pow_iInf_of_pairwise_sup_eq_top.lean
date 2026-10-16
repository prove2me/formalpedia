-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_iInf_pow_eq_pow_iInf_of_pairwise_sup_eq_top
-- name    : OAI.PiExponent.LogarithmicJetIdeals.iInf_pow_eq_pow_iInf_of_pairwise_sup_eq_top
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T21:05:32.56549+00:00
-- url     : https://prove2.me/theorems/f57c8556-934d-433d-a6dc-e34ebc23b2c0
-- title:
--   Powers of a finite infimum of comaximal ideals
-- statement:
--   For a finite pairwise comaximal family of ideals in a commutative semiring, the infimum of their nth powers equals the nth power of their infimum.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.Ideal.Operations

theorem OAI.PiExponent.LogarithmicJetIdeals.iInf_pow_eq_pow_iInf_of_pairwise_sup_eq_top
    {R : Type*} [CommSemiring R] (K : ℕ) (I : Fin K → Ideal R) (n : ℕ)
    (hpair : ∀ j k : Fin K, j ≠ k → I j ⊔ I k = ⊤) :
    (⨅ j : Fin K, I j ^ n) = (⨅ j : Fin K, I j) ^ n := by sorry
