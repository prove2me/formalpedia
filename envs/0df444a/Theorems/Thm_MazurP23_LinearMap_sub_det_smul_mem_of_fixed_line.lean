-- Prove2me | Theorems.Thm_MazurP23_LinearMap_sub_det_smul_mem_of_fixed_line
-- name    : MazurP23.LinearMap.sub_det_smul_mem_of_fixed_line
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-14T23:32:23.525537+00:00
-- url     : https://prove2.me/theorems/3e61ff27-639f-43fa-a453-a226be91355d
-- title:
--   Fixed line and determinant in dimension two
-- statement:
--   If a linear endomorphism f of a two-dimensional vector space V fixes a line C pointwise, then f x - det(f) x lies in C for every x in V.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean

import Mathlib

namespace MazurP23.LinearMap
theorem sub_det_smul_mem_of_fixed_line
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (h2 : Module.finrank F V = 2) (f : V →ₗ[F] V)
    (C : Submodule F V) (hC : Module.finrank F C = 1)
    (hfix : ∀ x ∈ C, f x = x) (x : V) :
    f x - LinearMap.det f • x ∈ C := by sorry
end MazurP23.LinearMap
