-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_tendsto_haar_special_negative
-- name    : FourierJacobi.Analysis.tendsto_haar_special_negative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:41:16.058745+00:00
-- url     : https://prove2.me/theorems/9cf164aa-63c0-494d-8f88-c9c2c3b0dab5
-- title:
--   Analysis: tendsto haar special negative
-- statement:
--   The Analysis construction uses the tendsto haar special negative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLimits.lean#L110-L126
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLimits.lean#L110-L126

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

theorem FourierJacobi.Analysis.tendsto_haar_special_negative
    (a b : ℂ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1)
    (haM : a ≠ -1) (hbM : b ≠ -1)
    (π : Kˣ) (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) :
    Tendsto (fun T => ((1 - (-1 : ℂ)) / ((qK : ℂ) + 1)) *
      paperExplicitHaarCore K a b (-(inverseSqrt qK : ℂ)) T π)
      (𝓝[Set.Ioo 0 1] 1)
      (𝓝 (((1 - (-1 : ℂ)) / ((qK : ℂ) + 1)) *
        paperE qK a b (-(inverseSqrt qK : ℂ)))) := by sorry
