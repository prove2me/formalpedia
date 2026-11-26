-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_haarLatticeCell_measure_ne_top
-- name    : FourierJacobi.Analysis.haarLatticeCell_measure_ne_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:36:31.52095+00:00
-- url     : https://prove2.me/theorems/22e78432-da28-47b8-8211-aa5e9078f29f
-- title:
--   Analysis: haar Lattice Cell measure ne top
-- statement:
--   The Analysis construction uses the haar Lattice Cell measure ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellMass.lean#L64-L70
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellMass.lean#L64-L70

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
variable [MeasurableSpace K] [BorelSpace K]
attribute [local instance] FourierJacobi.Analysis.haarCellMass_t2Space
attribute [local instance] FourierJacobi.Analysis.haarCellMass_secondCountable
attribute [local instance] FourierJacobi.Analysis.haarCellMass_unitsBorel
attribute [local instance] FourierJacobi.Analysis.haarCellMass_additiveSigmaFinite

theorem FourierJacobi.Analysis.haarLatticeCell_measure_ne_top (r : ℤ) (z : K) (i : LatticeIndex) :
    paperCoreMeasure K (haarLatticeCell K r z i) ≠ ⊤ := by sorry
