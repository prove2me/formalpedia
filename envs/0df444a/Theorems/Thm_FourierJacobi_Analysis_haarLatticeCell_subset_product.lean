-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_haarLatticeCell_subset_product
-- name    : FourierJacobi.Analysis.haarLatticeCell_subset_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:38:43.720713+00:00
-- url     : https://prove2.me/theorems/7f1c8dac-8109-571a-a5f6-8cf4abd09a47
-- title:
--   Analysis: haar Lattice Cell subset product
-- statement:
--   The Analysis construction uses the haar Lattice Cell subset product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellMass.lean#L35-L39
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellMass.lean#L35-L39

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

theorem FourierJacobi.Analysis.haarLatticeCell_subset_product (r : ℤ) (z : K) (k j h : ℤ) (c : ℕ) :
    haarLatticeCell K r z (k,j,h,c) ⊆
      unitValuationShell K k ×ˢ (integerShell K j ×ˢ integerShell K h) := by sorry
