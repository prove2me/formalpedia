-- Prove2me | Theorems.Thm_NewtonianLipschitz_matrix3_mulVec_tangent_one_norm_le
-- name    : NewtonianLipschitz.matrix3_mulVec_tangent_one_norm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:53:59.185238+00:00
-- url     : https://prove2.me/theorems/bc491b46-61b3-4739-bcc2-f762f7eea691
-- title:
--   Newtonian Lipschitz: matrix3 mul Vec tangent one norm le
-- statement:
--   Matrix action estimate when the SECOND input coordinate is
--   zero; the relevant row sum uses only columns 0 and 2.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialAllAxes.lean#L61-L95
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialAllAxes.lean#L61-L95

module
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialFirstAxis
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialAllAxes
set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz

theorem NewtonianLipschitz.matrix3_mulVec_tangent_one_norm_le
    (A : Matrix (Fin 3) (Fin 3) ℝ) (h : Vec3)
    (hzero : h 1 = 0) (B : ℝ) (hB : 0 ≤ B)
    (hrows : ∀ k : Fin 3, |A k 0| + |A k 2| ≤ B) :
    ‖A *ᵥ h‖ ≤ B * ‖h‖ := by sorry
