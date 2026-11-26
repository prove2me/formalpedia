-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_corrected_special_haar_comparison
-- name    : FourierJacobi.Analysis.corrected_special_haar_comparison
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:41:13.082093+00:00
-- url     : https://prove2.me/theorems/88692194-4701-4c3a-9af3-b2bc12fca66a
-- title:
--   Analysis: corrected special haar comparison
-- statement:
--   Corrected RHS(80) = RHS(191), with no extra factor, for the whole signed
--   product of actual damped explicit-kernel Haar integrals.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLimits.lean#L130-L145
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLimits.lean#L130-L145

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

theorem FourierJacobi.Analysis.corrected_special_haar_comparison
    (a b ε : ℂ) (hq : 2 < qK) (hε : ε = 1 ∨ ε = -1)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1)
    (haε : a ≠ ε) (hbε : b ≠ ε)
    (π : Kˣ) (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) :
    Tendsto (fun T => ((1 - ε) / ((qK : ℂ) + 1)) *
      paperExplicitHaarCore K a b (ε * (inverseSqrt qK : ℂ)) T π)
      (𝓝[Set.Ioo 0 1] 1)
      (𝓝 (((1 - ε) / ((qK : ℂ) + 1)) *
        paperE qK a b (ε * (inverseSqrt qK : ℂ)))) := by sorry
