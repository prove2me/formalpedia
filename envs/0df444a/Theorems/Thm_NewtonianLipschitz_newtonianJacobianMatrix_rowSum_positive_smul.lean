-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_rowSum_positive_smul
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_rowSum_positive_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:34:59.389382+00:00
-- url     : https://prove2.me/theorems/ddc495b0-0ad5-43a2-be88-836be4cbee87
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix row Sum positive smul
-- statement:
--   Scaling by a positive factor c scales every absolute Jacobian
--   row sum by c^(-3), provided the original displacement is nonzero.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianNormalization.lean#L20-L39
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianNormalization.lean#L20-L39

module
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations
public import Definitions.Def_NewtonianLipschitz_JacobianNormalization
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_rowSum_positive_smul
    (μ c : ℝ) (x : Vec3) (i : Fin 3)
    (hc : 0 < c) (hx : x ≠ 0) :
    (∑ j : Fin 3, |newtonianJacobianMatrix μ (c • x) i j|) =
      (1 / c ^ 3) *
        (∑ j : Fin 3, |newtonianJacobianMatrix μ x i j|) := by sorry
