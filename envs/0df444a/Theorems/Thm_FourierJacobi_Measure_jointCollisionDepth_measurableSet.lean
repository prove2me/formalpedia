-- Prove2me | Theorems.Thm_FourierJacobi_Measure_jointCollisionDepth_measurableSet
-- name    : FourierJacobi.Measure.jointCollisionDepth_measurableSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:33:49.476472+00:00
-- url     : https://prove2.me/theorems/54b5b7ca-1d82-40b2-9656-3bc66324a456
-- title:
--   Measure: joint Collision Depth measurable Set
-- statement:
--   The Measure construction uses the joint Collision Depth measurable Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L173-L181
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L173-L181

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
variable [MeasurableSpace K] [BorelSpace K]
attribute [local instance] FourierJacobi.Measure.jointCollision_secondCountable
attribute [local instance] FourierJacobi.Measure.jointCollision_additiveHaar_sigmaFinite

theorem FourierJacobi.Measure.jointCollisionDepth_measurableSet (z : K) (j h s : ℤ) (c : ℕ) :
    MeasurableSet (jointCollisionDepth K z j h s c) := by sorry
