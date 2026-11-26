-- Prove2me | Theorems.Thm_FourierJacobi_Measure_unitValuationShell_isOpen
-- name    : FourierJacobi.Measure.unitValuationShell_isOpen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:52:59.595068+00:00
-- url     : https://prove2.me/theorems/ec6c800c-c96b-5726-9437-03ac0bce8d01
-- title:
--   Measure: unit Valuation Shell is Open
-- statement:
--   The Measure construction uses the unit Valuation Shell is Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/MultiplicativeHaar.lean#L84-L87
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/MultiplicativeHaar.lean#L84-L87

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

theorem FourierJacobi.Measure.unitValuationShell_isOpen (n : ℤ) : IsOpen (unitValuationShell K n) := by sorry
