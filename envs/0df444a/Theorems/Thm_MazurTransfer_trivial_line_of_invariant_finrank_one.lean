-- Prove2me | Theorems.Thm_MazurTransfer_trivial_line_of_invariant_finrank_one
-- name    : MazurTransfer.trivial_line_of_invariant_finrank_one
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-14T20:50:11.861199+00:00
-- url     : https://prove2.me/theorems/bb2b7ed8-1a86-4f4b-b735-e1397b77662c
-- title:
--   A one-dimensional invariant space is an equivariant trivial line
-- statement:
--   Let k be a field, G a group, and V a finite-dimensional k-linear representation of G. If the G-invariant subspace has dimension one, then there is an injective equivariant linear map from the trivial representation on k to V, whose image equals the entire invariant subspace. The result constructs the actual fixed line used in the order-13 norm-kernel descent.
-- source:
--   Owned MazurTheorem integration, Apache-2.0, RepresentationInvariantLine.hasTrivialInvariantLine_of_finrank_one. Uses Mathlib at exact pin 0df444a360eaa60ab8c11dca51a86af692955474: Representation.invariants in Mathlib/RepresentationTheory/Invariants.lean, LinearEquiv.ofFinrankEq in Mathlib/LinearAlgebra/Dimension/Free.lean, and LinearMap.intertwiningMap_of_isIntertwiningMap in Mathlib/RepresentationTheory/Intertwining.lean.

import Mathlib.RepresentationTheory.Invariants

theorem MazurTransfer.trivial_line_of_invariant_finrank_one
    (k G V : Type*) [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) [Module.Finite k V]
    (h : Module.finrank k ρ.invariants = 1) :
    ∃ f : Representation.IntertwiningMap (Representation.trivial k G k) ρ,
      Function.Injective f ∧ LinearMap.range f.toLinearMap = ρ.invariants := by sorry
