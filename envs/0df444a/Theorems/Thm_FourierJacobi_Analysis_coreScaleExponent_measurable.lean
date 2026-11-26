-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_coreScaleExponent_measurable
-- name    : FourierJacobi.Analysis.coreScaleExponent_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:36:38.019222+00:00
-- url     : https://prove2.me/theorems/0c6208ee-b554-44c9-b39d-c9ac9489ca64
-- title:
--   Analysis: core Scale Exponent measurable
-- statement:
--   The Analysis construction uses the core Scale Exponent measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarKernel.lean#L105-L114
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarKernel.lean#L105-L114

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

theorem FourierJacobi.Analysis.coreScaleExponent_measurable : Measurable (coreScaleExponent K) := by sorry
