-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_allRows_le_candidateMaximum
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_normalized_allRows_le_candidateMaximum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:33:56.257298+00:00
-- url     : https://prove2.me/theorems/743c8f0e-2511-4b3c-ad31-60d85f9e1aa4
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix normalized all Rows le candidate Maximum
-- statement:
--   All three rows of the exact physical Jacobian obey the sharp
--   candidate bound in the nonnegative normalized octant.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/NormalizedSharpBound.lean#L278-L291
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/NormalizedSharpBound.lean#L278-L291

module
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_normalized_allRows_le_candidateMaximum
    (μ u v : ℝ) (hμ : 0 ≤ μ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (i : Fin 3) :
    (∑ j : Fin 3,
      |newtonianJacobianMatrix μ (normalizedVector u v) i j|) ≤
      μ * candidateMaximum := by sorry
