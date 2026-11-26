-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_haarLatticeCell_existsUnique
-- name    : FourierJacobi.Analysis.haarLatticeCell_existsUnique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:37:19.276275+00:00
-- url     : https://prove2.me/theorems/cd42a980-45ea-4d81-9593-92fed128ae42
-- title:
--   Analysis: haar Lattice Cell exists Unique
-- statement:
--   Every actual point off the known null set lies in exactly one lattice fibre.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLatticePartition.lean#L153-L160
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLatticePartition.lean#L153-L160

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
omit [MeasurableSpace K] [BorelSpace K]

theorem FourierJacobi.Analysis.haarLatticeCell_existsUnique (r : ℤ) (z : K) (hz : CentralRepresentative K r z)
    (p : HaarPoint K) (hp : p.2.1≠0 ∧ p.2.2≠0 ∧ p.2.2^2-p.2.1*z≠0) :
    ∃! i : LatticeIndex, p ∈ haarLatticeCell K r z i := by sorry
