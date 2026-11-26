-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_explicitWeylKernel_damping
-- name    : FourierJacobi.Analysis.explicitWeylKernel_damping
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:42:19.098851+00:00
-- url     : https://prove2.me/theorems/19527133-16bc-570d-acba-11aa633108bc
-- title:
--   Analysis: explicit Weyl Kernel damping
-- statement:
--   The Analysis construction uses the explicit Weyl Kernel damping property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ExplicitKernel.lean#L105-L111
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ExplicitKernel.lean#L105-L111

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

theorem FourierJacobi.Analysis.explicitWeylKernel_damping (t a b T : ℂ) (p : KernelPoint K) (hT : T ≠ 0) :
    T ^ (kernelHeight K p) * explicitWeylKernel K t a b p =
      (poincare t)⁻¹ * ∑ i : Fin 8,
        weylWeights t a b i * t ^ (6 * kernelN K p + 4 * kernelB K p) *
          (T * weylU a b i) ^ (kernelN K p) *
            (T * weylV a b i) ^ (kernelB K p) := by sorry
