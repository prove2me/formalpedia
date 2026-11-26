-- Prove2me | Theorems.Thm_FourierJacobi_Measure_canonicalValuation_uniformizer_smul
-- name    : FourierJacobi.Measure.canonicalValuation_uniformizer_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:43:03.741526+00:00
-- url     : https://prove2.me/theorems/691d5bae-c52a-41b3-9e6e-bb6a4181ee7d
-- title:
--   Measure: canonical Valuation uniformizer smul
-- statement:
--   The Measure construction uses the canonical Valuation uniformizer smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L159-L166
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L159-L166

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

theorem FourierJacobi.Measure.canonicalValuation_uniformizer_smul (π : 𝒪[K])
    (hπ : localFieldValuation K (π : K) = 1) (n : ℤ) (x : K) :
    localFieldValuation K ((canonicalUniformizerUnit K π hπ ^ n) • x) =
      (n : WithTop ℤ) + localFieldValuation K x := by sorry
