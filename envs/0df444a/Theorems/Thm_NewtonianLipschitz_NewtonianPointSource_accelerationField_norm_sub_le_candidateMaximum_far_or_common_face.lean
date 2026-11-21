-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_norm_sub_le_candidateMaximum_far_or_common_face
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_sub_le_candidateMaximum_far_or_common_face
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:58:07.673459+00:00
-- url     : https://prove2.me/theorems/8d742eac-1c42-496e-9f6f-886f9c574b15
-- title:
--   Newtonian Point Source: acceleration Field norm sub le candidate Maximum far or common face
-- statement:
--   The verified long-separation case R038 and the common-face
--   case R039 together cover all endpoint pairs satisfying
--   either condition. The excluded case is a *short* pair
--   without any shared safe supporting face.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CommonSafeFace.lean#L101-L116
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CommonSafeFace.lean#L101-L116

module
public import Definitions.Def_NewtonianLipschitz_LongSeparation
public import Definitions.Def_NewtonianLipschitz_CommonSafeFace
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_sub_le_candidateMaximum_far_or_common_face
    (c : NewtonianPointSource) (x y : Vec3) (d : ℝ)
    (hd : 0 < d)
    (hx : d ≤ ‖x‖) (hy : d ≤ ‖y‖)
    (hcases : d ≤ ‖x - y‖ ∨
      ∃ i : Fin 3,
        (d ≤ x i ∧ d ≤ y i) ∨
        (x i ≤ -d ∧ y i ≤ -d)) :
    ‖c.accelerationField x - c.accelerationField y‖ ≤
      ((1 / d ^ 3) * (c.gravitationalParameter * candidateMaximum)) *
        ‖x - y‖ := by sorry
