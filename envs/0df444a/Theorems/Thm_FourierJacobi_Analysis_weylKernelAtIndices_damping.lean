-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_weylKernelAtIndices_damping
-- name    : FourierJacobi.Analysis.weylKernelAtIndices_damping
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:34:32.498892+00:00
-- url     : https://prove2.me/theorems/26dedfb8-6de0-4934-9b0a-f9fa0b147a9a
-- title:
--   Analysis: weyl Kernel At Indices damping
-- statement:
--   The Analysis construction uses the weyl Kernel At Indices damping property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ExplicitKernel.lean#L49-L67
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ExplicitKernel.lean#L49-L67

import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ExplicitKernel
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations

theorem FourierJacobi.Analysis.weylKernelAtIndices_damping (t a b T : ℂ) (n B : ℤ) (hT : T ≠ 0) :
    T ^ (n+B) * weylKernelAtIndices t a b n B =
      (poincare t)⁻¹ * ∑ i : Fin 8,
        weylWeights t a b i * t ^ (6*n+4*B) *
          (T * weylU a b i) ^ n * (T * weylV a b i) ^ B := by sorry
