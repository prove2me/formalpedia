-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_weylKernelAtIndices_norm_le
-- name    : FourierJacobi.Analysis.weylKernelAtIndices_norm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:36:02.946289+00:00
-- url     : https://prove2.me/theorems/deb3966c-6551-43da-8c40-957603cd5b57
-- title:
--   Analysis: weyl Kernel At Indices norm le
-- statement:
--   The Analysis construction uses the weyl Kernel At Indices norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ExplicitKernel.lean#L25-L41
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ExplicitKernel.lean#L25-L41

import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ExplicitKernel
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations

theorem FourierJacobi.Analysis.weylKernelAtIndices_norm_le (t a b : ℂ) (n B : ℤ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖weylKernelAtIndices t a b n B‖ ≤
      ((∑ i : Fin 8, ‖weylWeights t a b i‖) / ‖poincare t‖) *
        ‖t‖ ^ (6 * n + 4 * B) := by sorry
