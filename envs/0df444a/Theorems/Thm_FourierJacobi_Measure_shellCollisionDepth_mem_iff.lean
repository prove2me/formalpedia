-- Prove2me | Theorems.Thm_FourierJacobi_Measure_shellCollisionDepth_mem_iff
-- name    : FourierJacobi.Measure.shellCollisionDepth_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:37:13.016095+00:00
-- url     : https://prove2.me/theorems/8a00745f-a171-4bca-b049-c8767cca9c98
-- title:
--   Measure: shell Collision Depth mem iff
-- statement:
--   The Measure construction uses the shell Collision Depth mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L20-L34
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L20-L34

import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Measure_JointCollision
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.jointCollision_t2Space

theorem FourierJacobi.Measure.shellCollisionDepth_mem_iff (a x : K) (n : ℤ) (c : ℕ) :
    x ∈ shellCollisionDepth K a n c ↔
      localFieldValuation K x = (n : WithTop ℤ) ∧
        localFieldValuation K (x - a) = ((n + (c : ℤ) : ℤ) : WithTop ℤ) := by sorry
