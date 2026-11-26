-- Prove2me | Theorems.Thm_FourierJacobi_Measure_additiveHaar_real_shellCollisionDepth
-- name    : FourierJacobi.Measure.additiveHaar_real_shellCollisionDepth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:37:52.201664+00:00
-- url     : https://prove2.me/theorems/de8b496b-d487-4d2a-9070-825ecf41e384
-- title:
--   Measure: additive Haar real shell Collision Depth
-- statement:
--   The Measure construction uses the additive Haar real shell Collision Depth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L155-L162
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L155-L162

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

theorem FourierJacobi.Measure.additiveHaar_real_shellCollisionDepth (a : K) (n : ℤ) (c : ℕ)
    (ha : localFieldValuation K a = (n : WithTop ℤ)) :
    (additiveHaar K).real (shellCollisionDepth K a n c) =
      shellCollisionProbability K c * (additiveHaar K).real (integerShell K n) := by sorry
