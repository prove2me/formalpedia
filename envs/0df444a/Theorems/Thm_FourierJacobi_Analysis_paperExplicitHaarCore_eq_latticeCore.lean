-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_paperExplicitHaarCore_eq_latticeCore
-- name    : FourierJacobi.Analysis.paperExplicitHaarCore_eq_latticeCore
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:38:12.691864+00:00
-- url     : https://prove2.me/theorems/234e033e-a247-5e48-ac2a-08002442c8b5
-- title:
--   Analysis: paper Explicit Haar Core eq lattice Core
-- statement:
--   The actual three independently defined Haar integrals equal the independent
--   master series. No integral-to-series identity or integrability is assumed.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCoreAssembly.lean#L107-L116
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCoreAssembly.lean#L107-L116

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

theorem FourierJacobi.Analysis.paperExplicitHaarCore_eq_latticeCore
    (a b d : ℂ) (T : ℝ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 < T) (hT₁ : T ≤ 1) (hd₀ : inverseSqrt qK ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hstrict : T * inverseSqrt qK < ‖d‖) (π : Kˣ)
    (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) :
    paperExplicitHaarCore K a b d T π = latticeCore qK a b d T := by sorry
