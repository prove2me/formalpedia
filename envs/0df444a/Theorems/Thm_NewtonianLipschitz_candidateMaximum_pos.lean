-- Prove2me | Theorems.Thm_NewtonianLipschitz_candidateMaximum_pos
-- name    : NewtonianLipschitz.candidateMaximum_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:42:31.338474+00:00
-- url     : https://prove2.me/theorems/179d8cf9-12a7-429b-96a0-beb83496ad9a
-- title:
--   Newtonian Lipschitz: candidate Maximum pos
-- statement:
--   The exact candidate maximum is strictly positive.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/AdmissibleSecantPairs.lean#L26-L35
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/AdmissibleSecantPairs.lean#L26-L35

module
public import Definitions.Def_NewtonianLipschitz_AdmissibleCriticalDirection
public import Definitions.Def_NewtonianLipschitz_AdmissibleSecantPairs
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.candidateMaximum_pos : 0 < candidateMaximum := by sorry
