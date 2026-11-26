-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_coreAtCentral_measurable
-- name    : FourierJacobi.Analysis.coreAtCentral_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:36:31.997492+00:00
-- url     : https://prove2.me/theorems/d5fbc5e9-038f-539e-96fe-fa4bb3335fee
-- title:
--   Analysis: core At Central measurable
-- statement:
--   The Analysis construction uses the core At Central measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarKernel.lean#L117-L119
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarKernel.lean#L117-L119

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
variable [MeasurableSpace K] [BorelSpace K]
attribute [local instance] FourierJacobi.Analysis._p2m_local_instance_d9a05d5624_103
omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [BorelSpace K]

theorem FourierJacobi.Analysis.coreAtCentral_measurable (z : K) : Measurable (coreAtCentral K z) := by sorry
