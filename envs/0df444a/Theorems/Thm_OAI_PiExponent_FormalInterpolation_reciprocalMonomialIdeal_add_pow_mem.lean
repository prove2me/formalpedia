-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_reciprocalMonomialIdeal_add_pow_mem
-- name    : OAI.PiExponent.FormalInterpolation.reciprocalMonomialIdeal_add_pow_mem
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T22:55:01.816771+00:00
-- url     : https://prove2.me/theorems/0f6900af-b32d-4c96-874d-8101f1cd1d8d
-- title:
--   Perturbed coordinate powers have reciprocal weight at least one
-- statement:
--   In any commutative ring, a coordinate perturbed by a sufficiently high power of another coordinate has its prescribed power in the reciprocal-weight monomial ideal. Prove this by binomial expansion and the inequality (e_i-k)/e_i+tk/e_j ≥ 1. This removes the expansion step from the parent. Positivity is explicit; coincident indices remain valid, and dimension zero has no possible indices.

import Definitions.Def_OAI_PiExponent_ReciprocalMonomialIdeal

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.reciprocalMonomialIdeal_add_pow_mem
    {R : Type*} [CommRing R] {d : Nat}
    (x : Fin d → R) (e : Fin d → Nat) (he : ∀ k, 0 < e k)
    (i j : Fin d) (t : Nat) (ht : e j ≤ t * e i) (a : R) :
    (x i + x j ^ t * a) ^ e i ∈ reciprocalMonomialIdeal x e 1 := by sorry
