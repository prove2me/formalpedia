-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_haarLatticeCell_prefactor_value
-- name    : FourierJacobi.Analysis.haarLatticeCell_prefactor_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:40:11.370735+00:00
-- url     : https://prove2.me/theorems/1318650c-ac07-4057-97c5-d57f146f4450
-- title:
--   Analysis: haar Lattice Cell prefactor value
-- statement:
--   The scalar normalization uses the actual source-normalized Haar cell mass.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellMaster.lean#L58-L75
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellMaster.lean#L58-L75

import Definitions.Def_FourierJacobi_Analysis_HaarCellValue
import Definitions.Def_FourierJacobi_Analysis_HaarCellMass
import Definitions.Def_FourierJacobi_Analysis_HaarCellMaster
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]

theorem FourierJacobi.Analysis.haarLatticeCell_prefactor_value
    (hq : 1 < (FourierJacobi.Measure.residueCardinality K : ℝ))
    (a b d : ℂ) (T : ℝ) (hT : T ≠ 0) (r : Fin 3) (z : K)
    (hz : CentralRepresentative K (r.val : ℤ) z) (i : LatticeIndex) :
    coreIntegralPrefactor (FourierJacobi.Measure.residueCardinality K : ℝ) r *
        (((paperCoreMeasure K).real (haarLatticeCell K (r.val : ℤ) z i) : ℝ) : ℂ) *
        haarCellValue (FourierJacobi.Measure.residueCardinality K : ℝ) a b d T
          (r.val : ℤ) i =
      ∑ w : Fin 8,
        (weylWeights (inverseSqrt (FourierJacobi.Measure.residueCardinality K : ℝ) : ℂ)
          a b w / paperC (FourierJacobi.Measure.residueCardinality K : ℝ)) *
        masterTerm (FourierJacobi.Measure.residueCardinality K : ℂ)
          (inverseSqrt (FourierJacobi.Measure.residueCardinality K : ℝ) : ℂ)
          d (weylU a b w) (weylV a b w) (T : ℂ) (r.val : ℤ) i := by sorry
