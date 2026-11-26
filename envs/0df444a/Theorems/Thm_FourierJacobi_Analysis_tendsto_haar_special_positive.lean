-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_tendsto_haar_special_positive
-- name    : FourierJacobi.Analysis.tendsto_haar_special_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:40:15.512664+00:00
-- url     : https://prove2.me/theorems/32b52586-c032-53eb-afd4-c5b5428c488e
-- title:
--   Analysis: tendsto haar special positive
-- statement:
--   Direct zero-product limit. It neither requires nor asserts an ordinary
--   undamped endpoint Haar integral.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLimits.lean#L103-L108
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLimits.lean#L103-L108

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

theorem FourierJacobi.Analysis.tendsto_haar_special_positive (a b : ℂ) (π : Kˣ) :
    Tendsto (fun T => ((1 - (1 : ℂ)) / ((qK : ℂ) + 1)) *
      paperExplicitHaarCore K a b (inverseSqrt qK : ℂ) T π)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 0) := by sorry
