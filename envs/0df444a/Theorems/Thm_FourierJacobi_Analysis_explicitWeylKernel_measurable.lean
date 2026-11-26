-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_explicitWeylKernel_measurable
-- name    : FourierJacobi.Analysis.explicitWeylKernel_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:34:22.827188+00:00
-- url     : https://prove2.me/theorems/4217e98b-43a0-575f-b68f-f171e228296b
-- title:
--   Analysis: explicit Weyl Kernel measurable
-- statement:
--   The Analysis construction uses the explicit Weyl Kernel measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ExplicitKernel.lean#L116-L120
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ExplicitKernel.lean#L116-L120

import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ExplicitKernel
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]

theorem FourierJacobi.Analysis.explicitWeylKernel_measurable (t a b : ℂ) :
    Measurable (explicitWeylKernel K t a b) := by sorry
