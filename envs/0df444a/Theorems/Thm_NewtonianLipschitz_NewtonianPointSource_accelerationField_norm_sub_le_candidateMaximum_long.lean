-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_norm_sub_le_candidateMaximum_long
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_sub_le_candidateMaximum_long
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:44:57.418254+00:00
-- url     : https://prove2.me/theorems/67e647db-aa10-44ba-909d-6c35796dcaeb
-- title:
--   Newtonian Point Source: acceleration Field norm sub le candidate Maximum long
-- statement:
--   R038: if two safe endpoints are at least one clearance
--   radius apart in the Cartesian norm, their actual Newtonian
--   force difference obeys the C3 coefficient even when the
--   segment passes through the forbidden cube.
--
--   This theorem deliberately does not address ‖x-y‖ < d.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/LongSeparation.lean#L75-L121
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/LongSeparation.lean#L75-L121

module
public import Definitions.Def_NewtonianLipschitz_AdmissibleSecantPairs
public import Definitions.Def_NewtonianLipschitz_LongSeparation
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_sub_le_candidateMaximum_long
    (c : NewtonianPointSource)
    (x y : Vec3) (d : ℝ)
    (hd : 0 < d)
    (hx : d ≤ ‖x‖) (hy : d ≤ ‖y‖)
    (hsep : d ≤ ‖x - y‖) :
    ‖c.accelerationField x - c.accelerationField y‖ ≤
      ((1 / d ^ 3) *
        (c.gravitationalParameter * candidateMaximum)) *
          ‖x - y‖ := by sorry
