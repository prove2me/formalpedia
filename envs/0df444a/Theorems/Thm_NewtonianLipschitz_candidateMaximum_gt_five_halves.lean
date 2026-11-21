-- Prove2me | Theorems.Thm_NewtonianLipschitz_candidateMaximum_gt_five_halves
-- name    : NewtonianLipschitz.candidateMaximum_gt_five_halves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:48:56.784168+00:00
-- url     : https://prove2.me/theorems/4779c0a9-3c64-4bd9-b002-564ae258bf97
-- title:
--   Newtonian Lipschitz: candidate Maximum gt five halves
-- statement:
--   Exact rational separation between the sharp local
--   Newtonian coefficient and the two-hop 5/4+5/4 estimate.
--   The comparison is independent of the approximate decimal C3.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/TangentialAlgebra.lean#L101-L145
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/TangentialAlgebra.lean#L101-L145

module
public import Definitions.Def_NewtonianLipschitz_CrossFaceTwoHop
public import Definitions.Def_NewtonianLipschitz_TangentialAlgebra
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.candidateMaximum_gt_five_halves :
    (5 / 2 : ℝ) < candidateMaximum := by sorry
