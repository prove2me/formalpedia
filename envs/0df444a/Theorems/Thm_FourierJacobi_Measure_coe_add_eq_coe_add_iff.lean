-- Prove2me | Theorems.Thm_FourierJacobi_Measure_coe_add_eq_coe_add_iff
-- name    : FourierJacobi.Measure.coe_add_eq_coe_add_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:37:05.376891+00:00
-- url     : https://prove2.me/theorems/32292635-2d64-546f-bf24-0dc2430bddd5
-- title:
--   Measure: coe add eq coe add iff
-- statement:
--   The Measure construction uses the coe add eq coe add iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L36-L40
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L36-L40

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

theorem FourierJacobi.Measure.coe_add_eq_coe_add_iff (s n : ℤ) (v : WithTop ℤ) :
    (s : WithTop ℤ) + v = ((s + n : ℤ) : WithTop ℤ) ↔ v = (n : WithTop ℤ) := by sorry
