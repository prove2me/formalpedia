-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_haarLatticeCell_exhaustive
-- name    : FourierJacobi.Analysis.haarLatticeCell_exhaustive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:36:51.361514+00:00
-- url     : https://prove2.me/theorems/27dcd7ae-c951-594d-8884-1c426cbf70ef
-- title:
--   Analysis: haar Lattice Cell exhaustive
-- statement:
--   The Analysis construction uses the haar Lattice Cell exhaustive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLatticePartition.lean#L74-L106
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLatticePartition.lean#L74-L106

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

theorem FourierJacobi.Analysis.haarLatticeCell_exhaustive (r : ℤ) (z : K) (hz : CentralRepresentative K r z)
    (p : HaarPoint K) (hp : p.2.1 ≠ 0 ∧ p.2.2 ≠ 0 ∧ p.2.2^2-p.2.1*z ≠ 0) :
    ∃ i : LatticeIndex, p ∈ haarLatticeCell K r z i := by sorry
