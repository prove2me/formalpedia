-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_explicitCoreIntegrand_measurable
-- name    : FourierJacobi.Analysis.explicitCoreIntegrand_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:43:35.103893+00:00
-- url     : https://prove2.me/theorems/7cdb96b0-4b21-4440-a922-417fecf3601d
-- title:
--   Analysis: explicit Core Integrand measurable
-- statement:
--   The Analysis construction uses the explicit Core Integrand measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarKernel.lean#L121-L131
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarKernel.lean#L121-L131

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

theorem FourierJacobi.Analysis.explicitCoreIntegrand_measurable (q : ℝ) (a b d : ℂ) (T : ℝ) (z : K) :
    Measurable (explicitCoreIntegrand K q a b d T z) := by sorry
