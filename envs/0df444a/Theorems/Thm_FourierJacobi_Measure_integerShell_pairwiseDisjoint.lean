-- Prove2me | Theorems.Thm_FourierJacobi_Measure_integerShell_pairwiseDisjoint
-- name    : FourierJacobi.Measure.integerShell_pairwiseDisjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:48:53.42955+00:00
-- url     : https://prove2.me/theorems/3bcc99cb-fa3b-5184-a8ef-977cc69d2585
-- title:
--   Measure: integer Shell pairwise Disjoint
-- statement:
--   The Measure construction uses the integer Shell pairwise Disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L142-L147
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L142-L147

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open scoped ENNReal NNReal Pointwise WithZero
open FourierJacobi FourierJacobi.Measure
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.integerShells_t2Space

theorem FourierJacobi.Measure.integerShell_pairwiseDisjoint :
    Pairwise (fun m n : ℤ => Disjoint (integerShell K m) (integerShell K n)) := by sorry
