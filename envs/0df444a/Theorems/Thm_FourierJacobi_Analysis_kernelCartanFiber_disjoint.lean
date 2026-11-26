-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_kernelCartanFiber_disjoint
-- name    : FourierJacobi.Analysis.kernelCartanFiber_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:43:54.929235+00:00
-- url     : https://prove2.me/theorems/b9de3890-d4a2-41ae-8b86-06a99c4aec7a
-- title:
--   Analysis: kernel Cartan Fiber disjoint
-- statement:
--   The Analysis construction uses the kernel Cartan Fiber disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarKernel.lean#L143-L147
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarKernel.lean#L143-L147

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

theorem FourierJacobi.Analysis.kernelCartanFiber_disjoint {n B m C : ℤ} (h : (n,B) ≠ (m,C)) :
    Disjoint (kernelCartanFiber K n B) (kernelCartanFiber K m C) := by sorry
