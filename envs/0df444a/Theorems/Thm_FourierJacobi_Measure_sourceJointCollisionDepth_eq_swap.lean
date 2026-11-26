-- Prove2me | Theorems.Thm_FourierJacobi_Measure_sourceJointCollisionDepth_eq_swap
-- name    : FourierJacobi.Measure.sourceJointCollisionDepth_eq_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:33:55.135849+00:00
-- url     : https://prove2.me/theorems/0de0b9c8-4a7c-51c1-ae3d-8ed2e9300236
-- title:
--   Measure: source Joint Collision Depth eq swap
-- statement:
--   The Measure construction uses the source Joint Collision Depth eq swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L112-L122
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L112-L122

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

theorem FourierJacobi.Measure.sourceJointCollisionDepth_eq_swap (z : K) (j h s : ℤ) (c : ℕ)
    (hz : localFieldValuation K z = (s : WithTop ℤ)) :
    sourceJointCollisionDepth K z j h c =
      Prod.swap ⁻¹' jointCollisionDepth K z j h s c := by sorry
