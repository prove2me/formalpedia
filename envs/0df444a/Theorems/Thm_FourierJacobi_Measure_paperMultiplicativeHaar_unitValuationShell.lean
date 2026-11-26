-- Prove2me | Theorems.Thm_FourierJacobi_Measure_paperMultiplicativeHaar_unitValuationShell
-- name    : FourierJacobi.Measure.paperMultiplicativeHaar_unitValuationShell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:53:23.041582+00:00
-- url     : https://prove2.me/theorems/3fc4440b-ef2e-5ad2-9102-c3b6b98a5f34
-- title:
--   Measure: paper Multiplicative Haar unit Valuation Shell
-- statement:
--   The Measure construction uses the paper Multiplicative Haar unit Valuation Shell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/PaperMultiplicativeHaar.lean#L47-L51
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/PaperMultiplicativeHaar.lean#L47-L51

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

theorem FourierJacobi.Measure.paperMultiplicativeHaar_unitValuationShell (n : ℤ) :
    paperMultiplicativeHaar K (unitValuationShell K n) =
      ENNReal.ofReal (1 - (residueCardinality K : ℝ)⁻¹) := by sorry
