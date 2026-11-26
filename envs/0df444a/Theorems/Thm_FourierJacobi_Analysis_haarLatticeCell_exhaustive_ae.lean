-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_haarLatticeCell_exhaustive_ae
-- name    : FourierJacobi.Analysis.haarLatticeCell_exhaustive_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:37:09.250008+00:00
-- url     : https://prove2.me/theorems/4c92fb20-c3cf-5495-b0e0-9d4630a0fa35
-- title:
--   Analysis: haar Lattice Cell exhaustive ae
-- statement:
--   The Analysis construction uses the haar Lattice Cell exhaustive ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLatticePartition.lean#L162-L169
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLatticePartition.lean#L162-L169

import Definitions.Def_FourierJacobi_Analysis_HaarKernel
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Valuations_KernelShells
import Definitions.Def_FourierJacobi_Analysis_HaarLatticePartition
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Filter ValuativeRel
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
attribute [local instance] FourierJacobi.Analysis._p2m_local_instance_9fc63f53e5_126
attribute [local instance] FourierJacobi.Analysis._p2m_local_instance_9fc63f53e5_127

theorem FourierJacobi.Analysis.haarLatticeCell_exhaustive_ae (μ : Measure K) [μ.IsAddHaarMeasure]
    (ν : Measure Kˣ) (r : ℤ) (z : K) (hz : CentralRepresentative K r z) :
    ∀ᵐ p : HaarPoint K ∂ν.prod (μ.prod μ),
      ∃! i : LatticeIndex, p ∈ haarLatticeCell K r z i := by sorry
