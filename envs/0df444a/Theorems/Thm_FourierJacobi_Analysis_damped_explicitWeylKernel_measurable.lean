-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_damped_explicitWeylKernel_measurable
-- name    : FourierJacobi.Analysis.damped_explicitWeylKernel_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:42:39.289775+00:00
-- url     : https://prove2.me/theorems/ada169b4-9692-43ad-940e-13237f413525
-- title:
--   Analysis: damped explicit Weyl Kernel measurable
-- statement:
--   The Analysis construction uses the damped explicit Weyl Kernel measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ExplicitKernel.lean#L122-L126
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ExplicitKernel.lean#L122-L126

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

theorem FourierJacobi.Analysis.damped_explicitWeylKernel_measurable (t a b T : ℂ) :
    Measurable (fun p : KernelPoint K =>
      T ^ (kernelHeight K p) * explicitWeylKernel K t a b p) := by sorry
