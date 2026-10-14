-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_mem_iInf_pow_of_pairwise_isCoprime
-- name    : OAI.PiExponent.LogarithmicJetIdeals.mem_iInf_pow_of_pairwise_isCoprime
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T22:57:19.649896+00:00
-- url     : https://prove2.me/theorems/47a95248-0096-474a-b66a-ac725ce78df2
-- title:
--   Powers of finite comaximal intersections
-- statement:
--   For a finite pairwise comaximal family of ideals, membership in every nth power implies membership in the nth power of their infimum. The statement also covers the zeroth power and an empty index family.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.Ideal.Operations

theorem OAI.PiExponent.LogarithmicJetIdeals.mem_iInf_pow_of_pairwise_isCoprime
    {R : Type*} [CommSemiring R] (K n : ℕ) (I : Fin K → Ideal R)
    (hcoprime : ∀ i j : Fin K, i ≠ j → IsCoprime (I i) (I j))
    {x : R} (hx : ∀ i : Fin K, x ∈ (I i) ^ n) :
    x ∈ (⨅ i : Fin K, I i) ^ n := by sorry
