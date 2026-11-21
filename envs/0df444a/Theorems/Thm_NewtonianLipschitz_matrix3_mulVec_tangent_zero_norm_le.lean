-- Prove2me | Theorems.Thm_NewtonianLipschitz_matrix3_mulVec_tangent_zero_norm_le
-- name    : NewtonianLipschitz.matrix3_mulVec_tangent_zero_norm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:50:47.164281+00:00
-- url     : https://prove2.me/theorems/87f1eee1-28c4-4d3f-8e2e-dd691cf4c308
-- title:
--   Newtonian Lipschitz: matrix3 mul Vec tangent zero norm le
-- statement:
--   A matrix with small tangent-column row sums acts with the
--   same bound on every direction whose first coordinate vanishes.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialNormalized.lean#L208-L241
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialNormalized.lean#L208-L241

module
public import Definitions.Def_NewtonianLipschitz_SafePlaneReduction
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialNormalized
set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz

theorem NewtonianLipschitz.matrix3_mulVec_tangent_zero_norm_le
    (A : Matrix (Fin 3) (Fin 3) ℝ) (h : Vec3)
    (hzero : h 0 = 0) (B : ℝ) (hB : 0 ≤ B)
    (hrows : ∀ k : Fin 3, |A k 1| + |A k 2| ≤ B) :
    ‖A *ᵥ h‖ ≤ B * ‖h‖ := by sorry
