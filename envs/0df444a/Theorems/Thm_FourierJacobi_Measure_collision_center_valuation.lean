-- Prove2me | Theorems.Thm_FourierJacobi_Measure_collision_center_valuation
-- name    : FourierJacobi.Measure.collision_center_valuation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:37:25.088428+00:00
-- url     : https://prove2.me/theorems/8c752181-5199-417a-b056-fe6467b9dc64
-- title:
--   Measure: collision center valuation
-- statement:
--   The Measure construction uses the collision center valuation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L42-L49
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L42-L49

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

theorem FourierJacobi.Measure.collision_center_valuation (y z : K) (h j s : ℤ)
    (hy : localFieldValuation K y = (h : WithTop ℤ))
    (hz : localFieldValuation K z = (s : WithTop ℤ)) (hlocus : 2 * h = j + s) :
    localFieldValuation K (y ^ 2 / z) = (j : WithTop ℤ) := by sorry
