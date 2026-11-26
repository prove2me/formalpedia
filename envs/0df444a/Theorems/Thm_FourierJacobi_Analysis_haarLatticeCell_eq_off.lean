-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_haarLatticeCell_eq_off
-- name    : FourierJacobi.Analysis.haarLatticeCell_eq_off
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:38:16.826707+00:00
-- url     : https://prove2.me/theorems/3f849864-13f2-5312-a0b9-405b327edc16
-- title:
--   Analysis: haar Lattice Cell eq off
-- statement:
--   The Analysis construction uses the haar Lattice Cell eq off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellMass.lean#L17-L25
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellMass.lean#L17-L25

import Definitions.Def_FourierJacobi_Analysis_HaarLatticePartition
import Definitions.Def_FourierJacobi_Measure_JointCollision
import Definitions.Def_FourierJacobi_Analysis_HaarCellMass
set_option autoImplicit false
noncomputable section
open MeasureTheory
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Measure FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem FourierJacobi.Analysis.haarLatticeCell_eq_off (r : ℤ) (z : K) (k j h : ℤ) (c : ℕ)
    (he : r = 0 ∨ 2 * h ≠ j - r) :
    haarLatticeCell K r z (k,j,h,c) =
      if c = 0 then unitValuationShell K k ×ˢ (integerShell K j ×ˢ integerShell K h)
      else ∅ := by sorry
