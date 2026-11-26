-- Prove2me | Theorems.Thm_FourierJacobi_Measure_jointCollisionDepth_section
-- name    : FourierJacobi.Measure.jointCollisionDepth_section
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:37:36.429435+00:00
-- url     : https://prove2.me/theorems/e9c285cc-778c-49b8-bcaa-af2239f247de
-- title:
--   Measure: joint Collision Depth section
-- statement:
--   The Measure construction uses the joint Collision Depth section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L69-L81
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean#L69-L81

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

theorem FourierJacobi.Measure.jointCollisionDepth_section (y z : K) (j h s : ℤ) (c : ℕ)
    (hz : localFieldValuation K z = (s : WithTop ℤ)) :
    Prod.mk y ⁻¹' jointCollisionDepth K z j h s c =
      if localFieldValuation K y = (h : WithTop ℤ)
      then shellCollisionDepth K (y ^ 2 / z) j c else ∅ := by sorry
