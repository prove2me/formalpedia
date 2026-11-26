-- Prove2me | Theorems.Thm_FourierJacobi_Measure_shellConditionalMass_collisionDepth
-- name    : FourierJacobi.Measure.shellConditionalMass_collisionDepth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:37:39.343828+00:00
-- url     : https://prove2.me/theorems/730b8d10-dd9c-50c5-9253-7b312de02471
-- title:
--   Measure: shell Conditional Mass collision Depth
-- statement:
--   The Measure construction uses the shell Conditional Mass collision Depth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L146-L153
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L146-L153

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

theorem FourierJacobi.Measure.shellConditionalMass_collisionDepth (a : K) (n : ℤ) (c : ℕ)
    (ha : localFieldValuation K a = (n : WithTop ℤ)) :
    shellConditionalMass K n (shellCollisionDepth K a n c) = shellCollisionProbability K c := by sorry
