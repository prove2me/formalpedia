-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_explicitWeylKernel_formula
-- name    : FourierJacobi.Analysis.explicitWeylKernel_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:42:16.40785+00:00
-- url     : https://prove2.me/theorems/35935c02-5e77-47c5-bc8a-19430e3af013
-- title:
--   Analysis: explicit Weyl Kernel formula
-- statement:
--   The Analysis construction uses the explicit Weyl Kernel formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ExplicitKernel.lean#L78-L91
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ExplicitKernel.lean#L78-L91

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

theorem FourierJacobi.Analysis.explicitWeylKernel_formula (t a b : ℂ) (p : KernelPoint K) :
    explicitWeylKernel K t a b p =
      (poincare t)⁻¹ * ∑ i : Fin 8,
        weylWeights t a b i * t ^ (3 * kernelEll K p + 4 * kernelB K p) *
          (weylU a b i) ^ (kernelEll K p / 2) *
            (weylV a b i) ^ (kernelB K p) := by sorry
