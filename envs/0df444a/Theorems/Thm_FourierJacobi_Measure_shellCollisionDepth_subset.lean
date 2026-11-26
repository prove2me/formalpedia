-- Prove2me | Theorems.Thm_FourierJacobi_Measure_shellCollisionDepth_subset
-- name    : FourierJacobi.Measure.shellCollisionDepth_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:42:30.40549+00:00
-- url     : https://prove2.me/theorems/5889234c-a16e-4d8c-b881-e6d414392f98
-- title:
--   Measure: shell Collision Depth subset
-- statement:
--   The Measure construction uses the shell Collision Depth subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/ShellCollision.lean#L66-L68
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/ShellCollision.lean#L66-L68

import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Definitions.Def_FourierJacobi_Measure_ShellCollision
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.shellCollision_t2Space

theorem FourierJacobi.Measure.shellCollisionDepth_subset (a : K) (n : ℤ) (c : ℕ) :
    shellCollisionDepth K a n c ⊆ integerShell K n := by sorry
