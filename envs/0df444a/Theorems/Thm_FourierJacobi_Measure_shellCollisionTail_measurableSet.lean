-- Prove2me | Theorems.Thm_FourierJacobi_Measure_shellCollisionTail_measurableSet
-- name    : FourierJacobi.Measure.shellCollisionTail_measurableSet
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:43:27.710126+00:00
-- url     : https://prove2.me/theorems/573116d1-b6fd-41de-965b-d54f80aa839f
-- title:
--   Measure: shell Collision Tail measurable Set
-- statement:
--   The Measure construction uses the shell Collision Tail measurable Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/ShellCollision.lean#L81-L84
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/ShellCollision.lean#L81-L84

import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Definitions.Def_FourierJacobi_Measure_ShellCollision
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.shellCollision_t2Space
variable [MeasurableSpace K] [BorelSpace K]

theorem FourierJacobi.Measure.shellCollisionTail_measurableSet (a : K) (n : ℤ) (c : ℕ) :
    MeasurableSet (shellCollisionTail K a n c) := by sorry
