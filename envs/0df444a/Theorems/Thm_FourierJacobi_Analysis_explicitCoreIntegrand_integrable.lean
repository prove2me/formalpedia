-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_explicitCoreIntegrand_integrable
-- name    : FourierJacobi.Analysis.explicitCoreIntegrand_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:38:47.857932+00:00
-- url     : https://prove2.me/theorems/9e56b3ba-c77a-4541-80e6-de683af08ef7
-- title:
--   Analysis: explicit Core Integrand integrable
-- statement:
--   Ordinary (unprefactored) integrability is proved as well.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCoreAssembly.lean#L82-L91
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCoreAssembly.lean#L82-L91

import Definitions.Def_FourierJacobi_Analysis_CentralWeylSeries
import Definitions.Def_FourierJacobi_Analysis_FiberIntegration
import Definitions.Def_FourierJacobi_Analysis_HaarCellMaster
import Definitions.Def_FourierJacobi_Analysis_HaarCoreAssembly
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open MeasureTheory FourierJacobi.Algebra FourierJacobi.Valuations FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
local notation "qK" => (residueCardinality K : ℝ)
attribute [local instance] FourierJacobi.Analysis._p2m_local_instance_bcb4d405dd_25
attribute [local instance] FourierJacobi.Analysis._p2m_local_instance_bcb4d405dd_26
attribute [local instance] FourierJacobi.Analysis._p2m_local_instance_bcb4d405dd_27

theorem FourierJacobi.Analysis.explicitCoreIntegrand_integrable
    (a b d : ℂ) (T : ℝ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 < T) (hT₁ : T ≤ 1) (hd₀ : inverseSqrt qK ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hstrict : T * inverseSqrt qK < ‖d‖) (r : Fin 3) (z : K)
    (hz : CentralRepresentative K (r.val : ℤ) z) :
    Integrable (explicitCoreIntegrand K qK a b d T z) (paperCoreMeasure K) := by sorry
