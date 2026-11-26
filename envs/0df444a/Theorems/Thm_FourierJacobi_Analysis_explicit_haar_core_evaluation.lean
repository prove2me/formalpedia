-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_explicit_haar_core_evaluation
-- name    : FourierJacobi.Analysis.explicit_haar_core_evaluation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:49:06.70521+00:00
-- url     : https://prove2.me/theorems/78c870fe-c657-4e34-bc3f-960dbc0f51a9
-- title:
--   Analysis: explicit haar core evaluation
-- statement:
--   Complete actual explicit-kernel Haar-core theorem: all three ordinary
--   integrals are integrable, their unscaled sum is E_q, the literal quotient is
--   regular, and the damped core converges to this value.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLimits.lean#L150-L164
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLimits.lean#L150-L164

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

theorem FourierJacobi.Analysis.explicit_haar_core_evaluation
    (a b d : ℂ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hd₀ : inverseSqrt qK < ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1)
    (π : Kˣ) (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) :
    (∀ r : Fin 3, Integrable
      (explicitCoreIntegrand K qK a b d 1 (coreCentral K π r)) (paperCoreMeasure K)) ∧
    paperExplicitHaarCore K a b d 1 π = paperE qK a b d ∧
    paperC qK * paperD1 qK a b d * paperD2 qK a b d ≠ 0 ∧
    Tendsto (fun T => paperExplicitHaarCore K a b d T π)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 (paperE qK a b d)) := by sorry
