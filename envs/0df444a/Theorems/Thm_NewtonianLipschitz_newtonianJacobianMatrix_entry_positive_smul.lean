-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_entry_positive_smul
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_entry_positive_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:30:05.812179+00:00
-- url     : https://prove2.me/theorems/70d24eb6-af1a-4df9-b15d-47ac10b25ac7
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix entry positive smul
-- statement:
--   Under a positive spatial rescaling by c, each exact Newtonian
--   Jacobian entry is multiplied by c^(-3).
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSymmetries.lean#L86-L106
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSymmetries.lean#L86-L106

module
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_entry_positive_smul
    (μ c : ℝ) (x : Vec3) (i j : Fin 3)
    (hc : 0 < c) (hx : x ≠ 0) :
    newtonianJacobianMatrix μ (c • x) i j =
      (1 / c ^ 3) * newtonianJacobianMatrix μ x i j := by sorry
