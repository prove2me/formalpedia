-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_explicitHaarCoreShell_eq_centralLatticeCore
-- name    : FourierJacobi.Analysis.explicitHaarCoreShell_eq_centralLatticeCore
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:40:12.544992+00:00
-- url     : https://prove2.me/theorems/1313fcd8-15f2-49b9-9c13-b5ec0757537b
-- title:
--   Analysis: explicit Haar Core Shell eq central Lattice Core
-- statement:
--   The Analysis construction uses the explicit Haar Core Shell eq central Lattice Core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCoreAssembly.lean#L93-L103
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCoreAssembly.lean#L93-L103

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

theorem FourierJacobi.Analysis.explicitHaarCoreShell_eq_centralLatticeCore
    (a b d : ℂ) (T : ℝ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 < T) (hT₁ : T ≤ 1) (hd₀ : inverseSqrt qK ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hstrict : T * inverseSqrt qK < ‖d‖) (π : Kˣ)
    (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) (r : Fin 3) :
    explicitHaarCoreShell K (additiveHaar K) (paperMultiplicativeHaar K)
      qK a b d T π r = centralLatticeCore qK a b d T r := by sorry
