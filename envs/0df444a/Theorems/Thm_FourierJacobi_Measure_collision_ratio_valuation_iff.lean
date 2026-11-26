-- Prove2me | Theorems.Thm_FourierJacobi_Measure_collision_ratio_valuation_iff
-- name    : FourierJacobi.Measure.collision_ratio_valuation_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:37:33.982598+00:00
-- url     : https://prove2.me/theorems/f9280de9-e67d-4b0e-9b86-de5695718341
-- title:
--   Measure: collision ratio valuation iff
-- statement:
--   The Measure construction uses the collision ratio valuation iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L83-L104
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L83-L104

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

theorem FourierJacobi.Measure.collision_ratio_valuation_iff (x y z : K) (j s : ℤ) (c : ℕ)
    (hx : localFieldValuation K x = (j : WithTop ℤ))
    (hz : localFieldValuation K z = (s : WithTop ℤ)) :
    localFieldValuation K (y ^ 2 / (x * z) - 1) = ((c : ℤ) : WithTop ℤ) ↔
      localFieldValuation K (y ^ 2 - x * z) = ((j + s + (c : ℤ) : ℤ) : WithTop ℤ) := by sorry
