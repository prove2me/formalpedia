-- Prove2me | Theorems.Thm_FourierJacobi_Measure_additiveHaar_prod_sourceJointCollisionDepth
-- name    : FourierJacobi.Measure.additiveHaar_prod_sourceJointCollisionDepth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:45:36.859349+00:00
-- url     : https://prove2.me/theorems/adca0f46-1e31-5826-b6fd-6f1ebed876c3
-- title:
--   Measure: additive Haar prod source Joint Collision Depth
-- statement:
--   The Measure construction uses the additive Haar prod source Joint Collision Depth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L223-L231
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L223-L231

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

theorem FourierJacobi.Measure.additiveHaar_prod_sourceJointCollisionDepth (z : K) (j h s : ℤ) (c : ℕ)
    (hz : localFieldValuation K z = (s : WithTop ℤ)) (hlocus : 2 * h = j + s) :
    ((additiveHaar K).prod (additiveHaar K)) (sourceJointCollisionDepth K z j h c) =
      ENNReal.ofReal (shellCollisionProbability K c *
        (additiveHaar K).real (integerShell K j)) * additiveHaar K (integerShell K h) := by sorry
