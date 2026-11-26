-- Prove2me | Theorems.Thm_FourierJacobi_Measure_additiveHaar_real_prod_sourceJointCollisionDepth
-- name    : FourierJacobi.Measure.additiveHaar_real_prod_sourceJointCollisionDepth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:38:09.564284+00:00
-- url     : https://prove2.me/theorems/5e7c6e24-6747-4f14-97ac-44f789be8231
-- title:
--   Measure: additive Haar real prod source Joint Collision Depth
-- statement:
--   The exact source collision ratio has joint mass S² q^(-j-h) p_c.
--   The factors q^(-j) and q^(-h) retain integer powers throughout.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L235-L246
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L235-L246

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

theorem FourierJacobi.Measure.additiveHaar_real_prod_sourceJointCollisionDepth (z : K) (j h s : ℤ) (c : ℕ)
    (hz : localFieldValuation K z = (s : WithTop ℤ)) (hlocus : 2 * h = j + s) :
    ((additiveHaar K).prod (additiveHaar K)).real (sourceJointCollisionDepth K z j h c) =
      (1 - (residueCardinality K : ℝ)⁻¹) ^ 2 *
        ((residueCardinality K : ℝ) ^ (-j) * (residueCardinality K : ℝ) ^ (-h)) *
          shellCollisionProbability K c := by sorry
