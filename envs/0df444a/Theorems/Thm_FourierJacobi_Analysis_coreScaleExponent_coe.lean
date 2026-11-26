-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_coreScaleExponent_coe
-- name    : FourierJacobi.Analysis.coreScaleExponent_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:35:21.055928+00:00
-- url     : https://prove2.me/theorems/924dde76-3008-4402-9b9d-9a883db1cf99
-- title:
--   Analysis: core Scale Exponent coe
-- statement:
--   The Analysis construction uses the core Scale Exponent coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarKernel.lean#L33-L35
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarKernel.lean#L33-L35

import Definitions.Def_FourierJacobi_Analysis_ExplicitKernel
import Definitions.Def_FourierJacobi_Measure_PaperMultiplicativeHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_FourierJacobi_Analysis_HaarKernel
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem FourierJacobi.Analysis.coreScaleExponent_coe (a : Kˣ) :
    (coreScaleExponent K a : WithTop ℤ) = localFieldValuation K (a : K) := by sorry
