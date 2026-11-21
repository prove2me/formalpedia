-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_norm_sub_le_two_candidateMaximum_different_axes
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_sub_le_two_candidateMaximum_different_axes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:58:02.778833+00:00
-- url     : https://prove2.me/theorems/a44bd440-8204-4e0e-86e0-19f2c04234b4
-- title:
--   Newtonian Point Source: acceleration Field norm sub le two candidate Maximum different axes
-- statement:
--   R040: two endpoints with safe active coordinates
--   on *different axes* satisfy a global two-point Newtonian
--   bound with coefficient 2 C3. This applies even if their
--   straight connecting segment enters the forbidden cube.
--
--   The factor 2 is from two safe convex hops, and is not
--   asserted to be the optimal coefficient.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CrossFaceTwoHop.lean#L77-L141
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CrossFaceTwoHop.lean#L77-L141

module
public import Definitions.Def_NewtonianLipschitz_CommonSafeFace
public import Definitions.Def_NewtonianLipschitz_CrossFaceTwoHop
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_sub_le_two_candidateMaximum_different_axes
    (c : NewtonianPointSource) (x y : Vec3) (d : ℝ)
    (hd : 0 < d) (i j : Fin 3) (hij : i ≠ j)
    (hxi : d ≤ x i ∨ x i ≤ -d)
    (hyj : d ≤ y j ∨ y j ≤ -d) :
    ‖c.accelerationField x - c.accelerationField y‖ ≤
      (2 * ((1 / d ^ 3) *
        (c.gravitationalParameter * candidateMaximum))) * ‖x - y‖ := by sorry
