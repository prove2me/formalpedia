-- Prove2me | Theorems.Thm_FourierJacobi_Measure_paperMultiplicativeHaar_valuationRingUnits
-- name    : FourierJacobi.Measure.paperMultiplicativeHaar_valuationRingUnits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:53:52.842809+00:00
-- url     : https://prove2.me/theorems/df15c201-6fc7-5efe-9a54-6a29530cff78
-- title:
--   Measure: paper Multiplicative Haar valuation Ring Units
-- statement:
--   The Measure construction uses the paper Multiplicative Haar valuation Ring Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/PaperMultiplicativeHaar.lean#L41-L45
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/PaperMultiplicativeHaar.lean#L41-L45

import Definitions.Def_FourierJacobi_Measure_MultiplicativeHaar
import Definitions.Def_FourierJacobi_Measure_PaperMultiplicativeHaar
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel
open scoped ENNReal
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable [MeasurableSpace Kˣ] [BorelSpace Kˣ]

theorem FourierJacobi.Measure.paperMultiplicativeHaar_valuationRingUnits :
    paperMultiplicativeHaar K (valuationRingUnits K : Set Kˣ) =
      ENNReal.ofReal (1 - (residueCardinality K : ℝ)⁻¹) := by sorry
