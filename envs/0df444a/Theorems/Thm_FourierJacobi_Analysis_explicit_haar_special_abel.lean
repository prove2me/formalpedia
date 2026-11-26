-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_explicit_haar_special_abel
-- name    : FourierJacobi.Analysis.explicit_haar_special_abel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:49:04.136488+00:00
-- url     : https://prove2.me/theorems/ff58dd22-6c64-4e12-ac33-f6a636bd0978
-- title:
--   Analysis: explicit haar special abel
-- statement:
--   At the special boundary every damped integral is justified, and the whole
--   signed product has the requested limit. No undamped endpoint integrability
--   or summability appears among either the hypotheses or conclusions.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLimits.lean#L169-L193
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLimits.lean#L169-L193

import Definitions.Def_FourierJacobi_Analysis_HaarCoreAssembly
import Definitions.Def_FourierJacobi_Analysis_HaarLimits
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations FourierJacobi.Measure
open MeasureTheory Filter
open scoped Topology
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
local notation "qK" => (residueCardinality K : ℝ)

theorem FourierJacobi.Analysis.explicit_haar_special_abel
    (a b ε : ℂ) (hq : 2 < qK) (hε : ε = 1 ∨ ε = -1)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1)
    (haε : a ≠ ε) (hbε : b ≠ ε)
    (π : Kˣ) (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) :
    (∀ T ∈ Set.Ioo (0 : ℝ) 1, ∀ r : Fin 3,
      Integrable (explicitCoreIntegrand K qK a b (ε * (inverseSqrt qK : ℂ)) T
        (coreCentral K π r)) (paperCoreMeasure K)) ∧
    paperC qK * paperD1 qK a b (ε * (inverseSqrt qK : ℂ)) *
      paperD2 qK a b (ε * (inverseSqrt qK : ℂ)) ≠ 0 ∧
    Tendsto (fun T => ((1 - ε) / ((qK : ℂ) + 1)) *
      paperExplicitHaarCore K a b (ε * (inverseSqrt qK : ℂ)) T π)
      (𝓝[Set.Ioo 0 1] 1)
      (𝓝 (((1 - ε) / ((qK : ℂ) + 1)) *
        paperE qK a b (ε * (inverseSqrt qK : ℂ)))) := by sorry
