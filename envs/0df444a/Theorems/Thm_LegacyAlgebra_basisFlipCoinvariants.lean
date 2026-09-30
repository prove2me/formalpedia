-- Prove2me | Theorems.Thm_LegacyAlgebra_basisFlipCoinvariants
-- name    : LegacyAlgebra.basisFlipCoinvariants
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-06T05:38:22.096222+00:00
-- url     : https://prove2.me/theorems/ee20cacb-dcf8-4f24-a702-c0b3ce85b235
-- title:
--   Basis-flip criterion for vanishing coinvariants
-- statement:
--   Let ρ be a linear representation of a group G on a vector space V over a field k in which 2 is nonzero. Suppose V has a basis b such that, for every basis vector b_i, some element of G sends b_i to −b_i. Then the span of all differences ρ(g)v − v is V, so the coinvariant space is zero. The basis and group may be infinite.
-- source:
--   Unpublished research note class2_pure_braid_filter_assessment.md, section “Odd-primary no-go for the stationary-source family”; SHA-256 3138168576f237898231c34e54fc76869bbb5f4c2b820c00f73b62ebe2f9d907.

import Mathlib

set_option autoImplicit false

theorem LegacyAlgebra.basisFlipCoinvariants
    (k G V ι : Type*) [Field k] [Group G]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (b : Module.Basis ι k V)
    (hTwo : (2 : k) ≠ 0)
    (hFlip : ∀ i : ι, ∃ g : G, ρ g (b i) = -(b i)) :
    Representation.Coinvariants.ker ρ = ⊤ := by
  sorry
