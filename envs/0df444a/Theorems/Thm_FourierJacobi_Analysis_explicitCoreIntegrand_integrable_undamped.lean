-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_explicitCoreIntegrand_integrable_undamped
-- name    : FourierJacobi.Analysis.explicitCoreIntegrand_integrable_undamped
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:40:44.295472+00:00
-- url     : https://prove2.me/theorems/b3f479a1-96ad-463e-ba17-8657ff8b107b
-- title:
--   Analysis: explicit Core Integrand integrable undamped
-- statement:
--   The Analysis construction uses the explicit Core Integrand integrable undamped property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLimits.lean#L53-L61
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLimits.lean#L53-L61

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

theorem FourierJacobi.Analysis.explicitCoreIntegrand_integrable_undamped
    (a b d : ℂ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hd₀ : inverseSqrt qK < ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (π : Kˣ) (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) (r : Fin 3) :
    Integrable (explicitCoreIntegrand K qK a b d 1 (coreCentral K π r))
      (paperCoreMeasure K) := by sorry
