-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_norm_sub_le_candidateMaximum_common_face
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_sub_le_candidateMaximum_common_face
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:45:29.479381+00:00
-- url     : https://prove2.me/theorems/d9b2acc6-18c2-47d1-a9f0-33c40168cc8a
-- title:
--   Newtonian Point Source: acceleration Field norm sub le candidate Maximum common face
-- statement:
--   R039: the C3 finite-difference bound holds for any two
--   endpoints sharing a positive or negative safe supporting
--   halfspace, independent of their mutual distance.
--
--   The endpoint conditions themselves certify their clearance,
--   and convexity of the supporting halfspace certifies the
--   whole connecting segment.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CommonSafeFace.lean#L70-L95
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CommonSafeFace.lean#L70-L95

module
public import Definitions.Def_NewtonianLipschitz_LongSeparation
public import Definitions.Def_NewtonianLipschitz_CommonSafeFace
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_sub_le_candidateMaximum_common_face
    (c : NewtonianPointSource) (x y : Vec3) (d : ℝ)
    (hd : 0 < d)
    (hface : ∃ i : Fin 3,
      (d ≤ x i ∧ d ≤ y i) ∨
      (x i ≤ -d ∧ y i ≤ -d)) :
    ‖c.accelerationField x - c.accelerationField y‖ ≤
      ((1 / d ^ 3) * (c.gravitationalParameter * candidateMaximum)) *
        ‖x - y‖ := by sorry
