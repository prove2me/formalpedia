-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_haarLatticeCell_complex_mass
-- name    : FourierJacobi.Analysis.haarLatticeCell_complex_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:39:15.501544+00:00
-- url     : https://prove2.me/theorems/d5d3c6f3-8599-4e4e-abf1-dba97f56f2bd
-- title:
--   Analysis: haar Lattice Cell complex mass
-- statement:
--   The convenient complex-coercion interface matches the actual measure
--   with the independently defined master family's collision weight.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellMass.lean#L116-L125
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellMass.lean#L116-L125

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

theorem FourierJacobi.Analysis.haarLatticeCell_complex_mass (r : ℤ) (z : K) (hz : CentralRepresentative K r z)
    (i : LatticeIndex) :
    (((paperCoreMeasure K).real (haarLatticeCell K r z i) : ℝ) : ℂ) =
      (1 - (residueCardinality K : ℂ)⁻¹) ^ 3 *
        ((residueCardinality K : ℂ) ^ (-i.2.1) *
          (residueCardinality K : ℂ) ^ (-i.2.2.1)) *
            collisionWeight (residueCardinality K : ℂ) r i.2.1 i.2.2.1 i.2.2.2 := by sorry
