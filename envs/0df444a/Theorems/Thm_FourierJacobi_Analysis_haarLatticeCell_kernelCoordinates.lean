-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_haarLatticeCell_kernelCoordinates
-- name    : FourierJacobi.Analysis.haarLatticeCell_kernelCoordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:37:08.012643+00:00
-- url     : https://prove2.me/theorems/ab4603e5-7bb6-4b47-982e-eb1ba70742f3
-- title:
--   Analysis: haar Lattice Cell kernel Coordinates
-- statement:
--   The Analysis construction uses the haar Lattice Cell kernel Coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLatticePartition.lean#L108-L121
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLatticePartition.lean#L108-L121

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

theorem FourierJacobi.Analysis.haarLatticeCell_kernelCoordinates (r : ℤ) (z : K)
    (hz : CentralRepresentative K r z) (i : LatticeIndex)
    (p : HaarPoint K) (hp : p ∈ haarLatticeCell K r z i) :
    KernelShellCoordinates K (coreAtCentral K z p) r i.1 i.2.1 i.2.2.1 i.2.2.2 := by sorry
