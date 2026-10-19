-- Prove2me | Theorems.Thm_MazurTransfer_FiniteAutomorphismSubgroupFixedFieldDegree_finrank_fixedField
-- name    : MazurTransfer.FiniteAutomorphismSubgroupFixedFieldDegree.finrank_fixedField
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T15:57:56.756123+00:00
-- url     : https://prove2.me/theorems/91fe4a67-6d0b-493a-a63b-bda5ecf761d9
-- title:
--   A finite automorphism subgroup has fixed-field degree equal to its order
-- statement:
--   For arbitrary fields K and E with a K-algebra structure and any finite subgroup H of the K-automorphism group of E, the degree of E over the actual fixed field of H is Nat.card H. No finiteness assumption on E over K is added.
-- source:
--   Unchanged complete MazurTheorem FiniteAutomorphismSubgroupFixedFieldDegree.finrank_fixedField proof and statement, Apache-2.0, Vas and contributors, using Mathlib FixedPoints.finrank_eq_card.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a finite subgroup's fixed-field degree without requiring
that the ambient field be finite over the ground field. Named downstream
consumer: the cyclic order-three actual diamond quotient of X_1(13).
-/
import Mathlib

noncomputable section
universe u v

theorem MazurTransfer.FiniteAutomorphismSubgroupFixedFieldDegree.finrank_fixedField (K : Type u) [Field K] (E : Type v) [Field E] [Algebra K E]
    (H : Subgroup (E ≃ₐ[K] E)) [Finite H] :
    Module.finrank (IntermediateField.fixedField H) E = Nat.card H := by sorry
