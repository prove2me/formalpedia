-- Prove2me | Theorems.Thm_FourierJacobi_Measure_additiveHaar_prod_jointCollisionDepth
-- name    : FourierJacobi.Measure.additiveHaar_prod_jointCollisionDepth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:34:39.357847+00:00
-- url     : https://prove2.me/theorems/c0189784-3d53-49de-acc9-0874c38482e9
-- title:
--   Measure: additive Haar prod joint Collision Depth
-- statement:
--   The actual two-variable collision shell mass, using product Haar and
--   the determinant polynomial.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L185-L201
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L185-L201

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

theorem FourierJacobi.Measure.additiveHaar_prod_jointCollisionDepth (z : K) (j h s : ℤ) (c : ℕ)
    (hz : localFieldValuation K z = (s : WithTop ℤ)) (hlocus : 2 * h = j + s) :
    ((additiveHaar K).prod (additiveHaar K)) (jointCollisionDepth K z j h s c) =
      ENNReal.ofReal (shellCollisionProbability K c *
        (additiveHaar K).real (integerShell K j)) * additiveHaar K (integerShell K h) := by sorry
