-- Prove2me | Theorems.Thm_MazurTransfer_finrank_fixed_field_of_finite_automorphism_subgroup
-- name    : MazurTransfer.finrank_fixed_field_of_finite_automorphism_subgroup
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T14:51:39.292738+00:00
-- url     : https://prove2.me/theorems/8cb13a38-0bad-4e8b-aa5d-b568ad632096
-- title:
--   The fixed field of a finite automorphism subgroup has degree equal to its cardinality
-- statement:
--   For a field extension E/K and a finite subgroup H of its K-automorphisms, the degree of E over the fixed intermediate field E^H is the cardinality of H. There is no assumption that E is finite or algebraic over K. The proof uses Mathlib fixed-point field theory. The downstream consumer is the actual degree-three diamond quotient of the order-thirteen modular curve, whose ground-field extension is transcendental.
-- source:
--   Owned MazurTheorem integration lemma using Mathlib at 0df444a360eaa60ab8c11dca51a86af692955474; Apache-2.0.

import Mathlib
universe u v

theorem MazurTransfer.finrank_fixed_field_of_finite_automorphism_subgroup (K : Type u) [Field K] (E : Type v) [Field E] [Algebra K E]
    (H : Subgroup (E ≃ₐ[K] E)) [Finite H] :
    Module.finrank (IntermediateField.fixedField H) E = Nat.card H := by sorry
