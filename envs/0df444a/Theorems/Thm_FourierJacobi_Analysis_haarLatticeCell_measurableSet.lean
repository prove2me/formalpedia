-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_haarLatticeCell_measurableSet
-- name    : FourierJacobi.Analysis.haarLatticeCell_measurableSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:37:29.246128+00:00
-- url     : https://prove2.me/theorems/c2885f8b-e221-4662-abb8-5452aabba10b
-- title:
--   Analysis: haar Lattice Cell measurable Set
-- statement:
--   The Analysis construction uses the haar Lattice Cell measurable Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLatticePartition.lean#L129-L149
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLatticePartition.lean#L129-L149

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

theorem FourierJacobi.Analysis.haarLatticeCell_measurableSet (r : ℤ) (z : K) (i : LatticeIndex) :
    MeasurableSet (haarLatticeCell K r z i) := by sorry
