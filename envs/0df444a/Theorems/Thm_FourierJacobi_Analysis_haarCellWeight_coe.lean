-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_haarCellWeight_coe
-- name    : FourierJacobi.Analysis.haarCellWeight_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:39:16.555975+00:00
-- url     : https://prove2.me/theorems/717f8e82-065f-428a-9d3e-eeaa7c8a81e3
-- title:
--   Analysis: haar Cell Weight coe
-- statement:
--   The Analysis construction uses the haar Cell Weight coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellMass.lean#L46-L49
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellMass.lean#L46-L49

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

theorem FourierJacobi.Analysis.haarCellWeight_coe (r j h : ℤ) (c : ℕ) :
    (haarCellWeight K r j h c : ℂ) = collisionWeight (residueCardinality K : ℂ) r j h c := by sorry
