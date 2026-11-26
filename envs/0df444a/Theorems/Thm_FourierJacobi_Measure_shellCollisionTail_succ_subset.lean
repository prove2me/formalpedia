-- Prove2me | Theorems.Thm_FourierJacobi_Measure_shellCollisionTail_succ_subset
-- name    : FourierJacobi.Measure.shellCollisionTail_succ_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:44:43.25424+00:00
-- url     : https://prove2.me/theorems/4c89eaf1-d8fe-40f2-b64a-e2f3de49beed
-- title:
--   Measure: shell Collision Tail succ subset
-- statement:
--   The Measure construction uses the shell Collision Tail succ subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/ShellCollision.lean#L56-L64
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/ShellCollision.lean#L56-L64

import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Definitions.Def_FourierJacobi_Measure_ShellCollision
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.shellCollision_t2Space

theorem FourierJacobi.Measure.shellCollisionTail_succ_subset (a : K) (n : ℤ) (c : ℕ) :
    shellCollisionTail K a n (c + 1) ⊆ shellCollisionTail K a n c := by sorry
