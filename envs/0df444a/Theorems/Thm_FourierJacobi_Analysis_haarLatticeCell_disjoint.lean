-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_haarLatticeCell_disjoint
-- name    : FourierJacobi.Analysis.haarLatticeCell_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:35:35.653911+00:00
-- url     : https://prove2.me/theorems/f7fc620e-7e28-55e7-bb62-9698bfe38eb3
-- title:
--   Analysis: haar Lattice Cell disjoint
-- statement:
--   The Analysis construction uses the haar Lattice Cell disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLatticePartition.lean#L54-L72
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLatticePartition.lean#L54-L72

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

theorem FourierJacobi.Analysis.haarLatticeCell_disjoint (r : ℤ) (z : K) {i i' : LatticeIndex} (hii : i ≠ i') :
    Disjoint (haarLatticeCell K r z i) (haarLatticeCell K r z i') := by sorry
