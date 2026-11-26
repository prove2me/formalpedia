-- Prove2me | Theorems.Thm_FourierJacobi_Measure_canonicalUniformizer_distribHaarChar
-- name    : FourierJacobi.Measure.canonicalUniformizer_distribHaarChar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:43:10.787538+00:00
-- url     : https://prove2.me/theorems/913921f9-0d74-4cd5-9208-e7f49307fab9
-- title:
--   Measure: canonical Uniformizer distrib Haar Char
-- statement:
--   The Haar scaling factor of the canonical uniformizer is obtained from the
--   actual maximal-ideal volume, which was proved by finite additive index.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L210-L230
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L210-L230

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
variable [MeasurableSpace K] [BorelSpace K]
attribute [local instance] FourierJacobi.Measure.integerShells_additiveHaar_regular

theorem FourierJacobi.Measure.canonicalUniformizer_distribHaarChar (π : 𝒪[K])
    (hπ : localFieldValuation K (π : K) = 1) :
    distribHaarChar K (canonicalUniformizerUnit K π hπ) =
      (residueCardinality K : ℝ≥0)⁻¹ := by sorry
