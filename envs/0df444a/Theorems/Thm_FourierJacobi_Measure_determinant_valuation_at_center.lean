-- Prove2me | Theorems.Thm_FourierJacobi_Measure_determinant_valuation_at_center
-- name    : FourierJacobi.Measure.determinant_valuation_at_center
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:37:28.10339+00:00
-- url     : https://prove2.me/theorems/96d6bab5-45a3-48e7-ad54-5ca1de2fd608
-- title:
--   Measure: determinant valuation at center
-- statement:
--   The Measure construction uses the determinant valuation at center property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L51-L59
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L51-L59

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

theorem FourierJacobi.Measure.determinant_valuation_at_center (x y z : K) (s : ℤ)
    (hz : localFieldValuation K z = (s : WithTop ℤ)) :
    localFieldValuation K (y ^ 2 - x * z) =
      (s : WithTop ℤ) + localFieldValuation K (x - y ^ 2 / z) := by sorry
