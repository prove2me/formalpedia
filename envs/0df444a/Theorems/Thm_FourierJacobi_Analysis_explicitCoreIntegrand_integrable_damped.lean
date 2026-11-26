-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_explicitCoreIntegrand_integrable_damped
-- name    : FourierJacobi.Analysis.explicitCoreIntegrand_integrable_damped
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:41:00.285251+00:00
-- url     : https://prove2.me/theorems/db59862d-03bf-4dd7-acec-8c24e87de72d
-- title:
--   Analysis: explicit Core Integrand integrable damped
-- statement:
--   The Analysis construction uses the explicit Core Integrand integrable damped property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLimits.lean#L42-L51
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLimits.lean#L42-L51

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

theorem FourierJacobi.Analysis.explicitCoreIntegrand_integrable_damped
    (a b d : ℂ) (T : ℝ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 < T) (hT₁ : T < 1) (hd₀ : inverseSqrt qK ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (π : Kˣ) (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) (r : Fin 3) :
    Integrable (explicitCoreIntegrand K qK a b d T (coreCentral K π r))
      (paperCoreMeasure K) := by sorry
