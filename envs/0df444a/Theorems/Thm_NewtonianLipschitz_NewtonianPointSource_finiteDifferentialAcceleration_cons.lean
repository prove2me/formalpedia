-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_cons
-- name    : NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:21:57.026189+00:00
-- url     : https://prove2.me/theorems/51a0f4df-86a3-4dde-bc5a-98d999cd361c
-- title:
--   Newtonian Point Source: finite Differential Acceleration cons
-- statement:
--   The Newtonian Point Source construction uses the finite Differential Acceleration cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/FiniteSources.lean#L26-L32
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/FiniteSources.lean#L26-L32

module
public import Definitions.Def_NewtonianLipschitz_Field
public import Definitions.Def_NewtonianLipschitz_FiniteSources
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_cons
    (source : ℝ → NewtonianPointSource)
    (sources : List (ℝ → NewtonianPointSource)) (t : ℝ) (q : Vec3) :
    NewtonianPointSource.finiteDifferentialAcceleration (source :: sources) t q =
      (source t).exactDifferentialAcceleration q +
        NewtonianPointSource.finiteDifferentialAcceleration sources t q := by sorry
