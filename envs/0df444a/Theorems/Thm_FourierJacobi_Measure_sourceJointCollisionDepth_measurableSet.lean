-- Prove2me | Theorems.Thm_FourierJacobi_Measure_sourceJointCollisionDepth_measurableSet
-- name    : FourierJacobi.Measure.sourceJointCollisionDepth_measurableSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:45:33.947314+00:00
-- url     : https://prove2.me/theorems/f946c80a-b734-5d51-b04f-17f30002038a
-- title:
--   Measure: source Joint Collision Depth measurable Set
-- statement:
--   The Measure construction uses the source Joint Collision Depth measurable Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L217-L221
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L217-L221

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

theorem FourierJacobi.Measure.sourceJointCollisionDepth_measurableSet (z : K) (j h s : ℤ) (c : ℕ)
    (hz : localFieldValuation K z = (s : WithTop ℤ)) :
    MeasurableSet (sourceJointCollisionDepth K z j h c) := by sorry
