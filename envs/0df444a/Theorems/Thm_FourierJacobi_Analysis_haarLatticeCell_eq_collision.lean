-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_haarLatticeCell_eq_collision
-- name    : FourierJacobi.Analysis.haarLatticeCell_eq_collision
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:38:30.978301+00:00
-- url     : https://prove2.me/theorems/f572e225-b302-5d79-ab65-641ab65cb27e
-- title:
--   Analysis: haar Lattice Cell eq collision
-- statement:
--   The Analysis construction uses the haar Lattice Cell eq collision property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellMass.lean#L27-L33
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellMass.lean#L27-L33

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

theorem FourierJacobi.Analysis.haarLatticeCell_eq_collision (r : ℤ) (z : K) (k j h : ℤ) (c : ℕ)
    (he : ¬(r = 0 ∨ 2 * h ≠ j - r)) :
    haarLatticeCell K r z (k,j,h,c) =
      unitValuationShell K k ×ˢ sourceJointCollisionDepth K z j h c := by sorry
