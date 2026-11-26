-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_coreCentral_one
-- name    : FourierJacobi.Analysis.coreCentral_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:35:11.415265+00:00
-- url     : https://prove2.me/theorems/f490c210-4215-4455-8948-b842c18dc283
-- title:
--   Analysis: core Central one
-- statement:
--   The Analysis construction uses the core Central one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarKernel.lean#L80-L81
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarKernel.lean#L80-L81

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
omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem FourierJacobi.Analysis.coreCentral_one (π : Kˣ) : coreCentral K π 1 = (π : K)⁻¹ := by sorry
