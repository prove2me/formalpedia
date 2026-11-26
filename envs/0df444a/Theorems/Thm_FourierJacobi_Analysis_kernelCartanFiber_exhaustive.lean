-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_kernelCartanFiber_exhaustive
-- name    : FourierJacobi.Analysis.kernelCartanFiber_exhaustive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:44:02.51133+00:00
-- url     : https://prove2.me/theorems/19ed7fd5-7f1b-4329-bb99-d6127c2f7da8
-- title:
--   Analysis: kernel Cartan Fiber exhaustive
-- statement:
--   The Analysis construction uses the kernel Cartan Fiber exhaustive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarKernel.lean#L150-L151
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarKernel.lean#L150-L151

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
omit [MeasurableSpace K] [BorelSpace K]

theorem FourierJacobi.Analysis.kernelCartanFiber_exhaustive (p : KernelPoint K) :
    p ∈ kernelCartanFiber K (kernelN K p) (kernelB K p) := by sorry
