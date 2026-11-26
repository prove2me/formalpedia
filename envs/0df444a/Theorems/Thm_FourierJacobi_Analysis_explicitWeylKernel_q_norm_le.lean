-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_explicitWeylKernel_q_norm_le
-- name    : FourierJacobi.Analysis.explicitWeylKernel_q_norm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:42:49.486519+00:00
-- url     : https://prove2.me/theorems/8c2792f1-2e1d-544e-9274-63cfbff92865
-- title:
--   Analysis: explicit Weyl Kernel q norm le
-- statement:
--   The majorant q^(-3ℓ/2-2b), with the even Cartan exponent expressed by n=ℓ/2.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarKernel.lean#L44-L56
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarKernel.lean#L44-L56

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

theorem FourierJacobi.Analysis.explicitWeylKernel_q_norm_le (q : ℝ) (hq : 1 < q)
    (a b : ℂ) (p : KernelPoint K) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖explicitWeylKernel K (inverseSqrt q : ℂ) a b p‖ ≤
      ((∑ i : Fin 8, ‖weylWeights (inverseSqrt q : ℂ) a b i‖) /
        poincare (inverseSqrt q)) * q ^ (-3 * kernelN K p - 2 * kernelB K p) := by sorry
