-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_corrected_principal_haar_comparison
-- name    : FourierJacobi.Analysis.corrected_principal_haar_comparison
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:48:48.791742+00:00
-- url     : https://prove2.me/theorems/9cf2dd67-568c-4247-adf9-d586169bdb1a
-- title:
--   Analysis: corrected principal haar comparison
-- statement:
--   Corrected RHS(77) = [2/(q+1)] RHS(184), at the actual explicit-kernel
--   Haar scope. The spherical-coefficient identification remains a separate bridge.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLimits.lean#L88-L99
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLimits.lean#L88-L99

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

theorem FourierJacobi.Analysis.corrected_principal_haar_comparison
    (a b d : ℂ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hd₀ : inverseSqrt qK < ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1)
    (π : Kˣ) (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) :
    (2 / ((qK : ℂ) + 1) * paperExplicitHaarCore K a b d 1 π =
      2 / ((qK : ℂ) + 1) * paperE qK a b d) ∧
    Tendsto (fun T => 2 / ((qK : ℂ) + 1) * paperExplicitHaarCore K a b d T π)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 (2 / ((qK : ℂ) + 1) * paperE qK a b d)) := by sorry
