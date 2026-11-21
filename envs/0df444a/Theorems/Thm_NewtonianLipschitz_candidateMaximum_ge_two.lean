-- Prove2me | Theorems.Thm_NewtonianLipschitz_candidateMaximum_ge_two
-- name    : NewtonianLipschitz.candidateMaximum_ge_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:44:06.443689+00:00
-- url     : https://prove2.me/theorems/aaac00bc-3ae4-4ae5-80a3-a5616a384a59
-- title:
--   Newtonian Lipschitz: candidate Maximum ge two
-- statement:
--   The sharp coefficient is at least the axis-aligned
--   scalar value 2, independently of decimal approximations.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/LongSeparation.lean#L24-L32
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/LongSeparation.lean#L24-L32

module
public import Definitions.Def_NewtonianLipschitz_AdmissibleSecantPairs
public import Definitions.Def_NewtonianLipschitz_LongSeparation
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.candidateMaximum_ge_two : (2 : ℝ) ≤ candidateMaximum := by sorry
