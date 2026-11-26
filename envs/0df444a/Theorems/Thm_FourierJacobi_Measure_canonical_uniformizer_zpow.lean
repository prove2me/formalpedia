-- Prove2me | Theorems.Thm_FourierJacobi_Measure_canonical_uniformizer_zpow
-- name    : FourierJacobi.Measure.canonical_uniformizer_zpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:42:28.203481+00:00
-- url     : https://prove2.me/theorems/70b331e8-a6ba-5736-a200-ea18c223687e
-- title:
--   Measure: canonical uniformizer zpow
-- statement:
--   The Measure construction uses the canonical uniformizer zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L94-L100
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L94-L100

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

theorem FourierJacobi.Measure.canonical_uniformizer_zpow (π : 𝒪[K])
    (hπ : localFieldValuation K (π : K) = 1) (n : ℤ) :
    localFieldValuation K ((π : K) ^ n) = (n : WithTop ℤ) := by sorry
