-- Prove2me | Theorems.Thm_FourierJacobi_Measure_shellCollisionTail_eq_preimage
-- name    : FourierJacobi.Measure.shellCollisionTail_eq_preimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:42:58.789797+00:00
-- url     : https://prove2.me/theorems/d5a41e44-3783-5e5d-bafe-d93169c9d0c5
-- title:
--   Measure: shell Collision Tail eq preimage
-- statement:
--   The Measure construction uses the shell Collision Tail eq preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/ShellCollision.lean#L43-L54
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/ShellCollision.lean#L43-L54

import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Definitions.Def_FourierJacobi_Measure_ShellCollision
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.shellCollision_t2Space

theorem FourierJacobi.Measure.shellCollisionTail_eq_preimage (a : K) (n : ℤ) (c : ℕ)
    (ha : localFieldValuation K a = (n : WithTop ℤ)) (hc : 0 < c) :
    shellCollisionTail K a n c =
      (fun x : K => x - a) ⁻¹' integerBall K (n + c) := by sorry
