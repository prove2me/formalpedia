-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_integrable_prefactor_core_eq_centralLatticeCore
-- name    : FourierJacobi.Analysis.integrable_prefactor_core_eq_centralLatticeCore
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:38:36.481872+00:00
-- url     : https://prove2.me/theorems/1f622326-46c4-4964-bd39-9d7459e379c9
-- title:
--   Analysis: integrable prefactor core eq central Lattice Core
-- statement:
--   The source prefactor times each actual Haar integrand is integrable, and
--   its ordinary integral is the corresponding independent central lattice sum.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCoreAssembly.lean#L31-L79
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCoreAssembly.lean#L31-L79

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

theorem FourierJacobi.Analysis.integrable_prefactor_core_eq_centralLatticeCore
    (a b d : ℂ) (T : ℝ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 < T) (hT₁ : T ≤ 1) (hd₀ : inverseSqrt qK ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hstrict : T * inverseSqrt qK < ‖d‖) (r : Fin 3) (z : K)
    (hz : CentralRepresentative K (r.val : ℤ) z) :
    Integrable (fun p => coreIntegralPrefactor qK r *
      explicitCoreIntegrand K qK a b d T z p) (paperCoreMeasure K) ∧
    (∫ p, coreIntegralPrefactor qK r * explicitCoreIntegrand K qK a b d T z p
      ∂paperCoreMeasure K) = centralLatticeCore qK a b d T r := by sorry
