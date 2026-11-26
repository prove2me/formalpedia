-- Prove2me | Theorems.Thm_FourierJacobi_Measure_canonical_uniformizer_generates
-- name    : FourierJacobi.Measure.canonical_uniformizer_generates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:44:06.662995+00:00
-- url     : https://prove2.me/theorems/f1939033-c2fa-5563-8352-378d6234a992
-- title:
--   Measure: canonical uniformizer generates
-- statement:
--   Canonical additive valuation one implies generation of the actual maximal
--   ideal. Generation is proved here, not assumed as an extra local-field datum.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L73-L92
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L73-L92

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

theorem FourierJacobi.Measure.canonical_uniformizer_generates (π : 𝒪[K])
    (hπ : localFieldValuation K (π : K) = 1) : 𝓂[K] = Ideal.span {π} := by sorry
