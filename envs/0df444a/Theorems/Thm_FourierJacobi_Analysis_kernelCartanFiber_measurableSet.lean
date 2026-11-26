-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_kernelCartanFiber_measurableSet
-- name    : FourierJacobi.Analysis.kernelCartanFiber_measurableSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:43:31.608115+00:00
-- url     : https://prove2.me/theorems/e33fdb2f-54aa-4e88-9de0-582b36e1bfc1
-- title:
--   Analysis: kernel Cartan Fiber measurable Set
-- statement:
--   The Analysis construction uses the kernel Cartan Fiber measurable Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarKernel.lean#L137-L140
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarKernel.lean#L137-L140

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

theorem FourierJacobi.Analysis.kernelCartanFiber_measurableSet (n B : ℤ) :
    MeasurableSet (kernelCartanFiber K n B) := by sorry
