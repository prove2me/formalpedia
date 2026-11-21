-- Prove2me | Theorems.Thm_NewtonianLipschitz_cartesian_different_axes_two_hop_bridge
-- name    : NewtonianLipschitz.cartesian_different_axes_two_hop_bridge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:46:45.395038+00:00
-- url     : https://prove2.me/theorems/cecc3dc7-d67d-469c-b3a4-fb64afc7891f
-- title:
--   Newtonian Lipschitz: cartesian different axes two hop bridge
-- statement:
--   Replace the i-th coordinate of y with that of x.
--   When i ≠ j, this bridge agrees with x on coordinate i
--   and with y on coordinate j. Its two Cartesian hop
--   lengths are each no more than ‖x-y‖.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CrossFaceTwoHop.lean#L32-L68
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CrossFaceTwoHop.lean#L32-L68

module
public import Definitions.Def_NewtonianLipschitz_CommonSafeFace
public import Definitions.Def_NewtonianLipschitz_CrossFaceTwoHop
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.cartesian_different_axes_two_hop_bridge
    (x y : Vec3) (i j : Fin 3) (hij : i ≠ j) :
    ∃ w : Vec3,
      w i = x i ∧
      w j = y j ∧
      ‖x - w‖ ≤ ‖x - y‖ ∧
      ‖w - y‖ ≤ ‖x - y‖ := by sorry
