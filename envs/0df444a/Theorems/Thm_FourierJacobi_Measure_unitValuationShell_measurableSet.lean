-- Prove2me | Theorems.Thm_FourierJacobi_Measure_unitValuationShell_measurableSet
-- name    : FourierJacobi.Measure.unitValuationShell_measurableSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:53:30.068421+00:00
-- url     : https://prove2.me/theorems/fe1a9d28-e7bc-4878-a875-fb422f28acbf
-- title:
--   Measure: unit Valuation Shell measurable Set
-- statement:
--   The Measure construction uses the unit Valuation Shell measurable Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/MultiplicativeHaar.lean#L112-L113
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/MultiplicativeHaar.lean#L112-L113

import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Mathlib.Topology.Algebra.Group.Units
import Definitions.Def_FourierJacobi_Measure_MultiplicativeHaar
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open scoped ENNReal Pointwise
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.multiplicativeHaar_t2Space
variable [MeasurableSpace Kˣ] [BorelSpace Kˣ]

theorem FourierJacobi.Measure.unitValuationShell_measurableSet (n : ℤ) : MeasurableSet (unitValuationShell K n) := by sorry
