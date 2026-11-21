-- Prove2me | Theorems.Thm_NewtonianLipschitz_matrix3_mulVec_tangent_two_norm_le
-- name    : NewtonianLipschitz.matrix3_mulVec_tangent_two_norm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:54:09.086296+00:00
-- url     : https://prove2.me/theorems/ce754b74-6eab-4fa1-84c7-5746e20f384c
-- title:
--   Newtonian Lipschitz: matrix3 mul Vec tangent two norm le
-- statement:
--   Matrix action estimate when the THIRD input coordinate is
--   zero; the relevant row sum uses only columns 0 and 1.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialAllAxes.lean#L99-L133
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialAllAxes.lean#L99-L133

module
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialFirstAxis
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialAllAxes
set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz

theorem NewtonianLipschitz.matrix3_mulVec_tangent_two_norm_le
    (A : Matrix (Fin 3) (Fin 3) ℝ) (h : Vec3)
    (hzero : h 2 = 0) (B : ℝ) (hB : 0 ≤ B)
    (hrows : ∀ k : Fin 3, |A k 0| + |A k 1| ≤ B) :
    ‖A *ᵥ h‖ ≤ B * ‖h‖ := by sorry
