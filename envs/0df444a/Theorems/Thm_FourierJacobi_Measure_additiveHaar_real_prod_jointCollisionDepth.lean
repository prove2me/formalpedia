-- Prove2me | Theorems.Thm_FourierJacobi_Measure_additiveHaar_real_prod_jointCollisionDepth
-- name    : FourierJacobi.Measure.additiveHaar_real_prod_jointCollisionDepth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:38:07.359887+00:00
-- url     : https://prove2.me/theorems/af1c5825-dc77-4682-a6af-d6757351f45e
-- title:
--   Measure: additive Haar real prod joint Collision Depth
-- statement:
--   The Measure construction uses the additive Haar real prod joint Collision Depth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L203-L215
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L203-L215

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

theorem FourierJacobi.Measure.additiveHaar_real_prod_jointCollisionDepth (z : K) (j h s : ℤ) (c : ℕ)
    (hz : localFieldValuation K z = (s : WithTop ℤ)) (hlocus : 2 * h = j + s) :
    ((additiveHaar K).prod (additiveHaar K)).real (jointCollisionDepth K z j h s c) =
      shellCollisionProbability K c *
        ((1 - (residueCardinality K : ℝ)⁻¹) ^ 2 *
          ((residueCardinality K : ℝ) ^ (-j) * (residueCardinality K : ℝ) ^ (-h))) := by sorry
