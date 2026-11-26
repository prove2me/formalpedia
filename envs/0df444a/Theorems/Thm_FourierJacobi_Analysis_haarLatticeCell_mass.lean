-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_haarLatticeCell_mass
-- name    : FourierJacobi.Analysis.haarLatticeCell_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:46:27.27068+00:00
-- url     : https://prove2.me/theorems/2f676b49-a62b-5a05-8b4b-d7691c1828dd
-- title:
--   Analysis: haar Lattice Cell mass
-- statement:
--   The Analysis construction uses the haar Lattice Cell mass property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellMass.lean#L104-L112
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellMass.lean#L104-L112

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

theorem FourierJacobi.Analysis.haarLatticeCell_mass (r : ℤ) (z : K) (hz : CentralRepresentative K r z)
    (i : LatticeIndex) :
    paperCoreMeasure K (haarLatticeCell K r z i) =
      ENNReal.ofReal ((1 - (residueCardinality K : ℝ)⁻¹) ^ 3 *
        ((residueCardinality K : ℝ) ^ (-i.2.1) *
          (residueCardinality K : ℝ) ^ (-i.2.2.1)) *
            haarCellWeight K r i.2.1 i.2.2.1 i.2.2.2) := by sorry
