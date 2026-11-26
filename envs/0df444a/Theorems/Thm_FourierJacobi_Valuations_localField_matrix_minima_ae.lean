-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_localField_matrix_minima_ae
-- name    : FourierJacobi.Valuations.localField_matrix_minima_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:31:00.78913+00:00
-- url     : https://prove2.me/theorems/3815e0a0-9911-4246-9e53-c742c2c44609
-- title:
--   Valuations: local Field matrix minima ae
-- statement:
--   For a fixed nonzero a and a central coordinate of valuation -r, r≠0,
--   the actual matrix entry/minor minima are the integer-table minima almost
--   everywhere. The nonnegative collision depth is constructed from the actual
--   field ratio when the two terms have equal valuation, and is zero otherwise.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/LocalMatrix.lean#L25-L61
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/LocalMatrix.lean#L25-L61

import Definitions.Def_FourierJacobi_Valuations_MatrixBridge
import Definitions.Def_FourierJacobi_Measure_NullSets
import Definitions.Def_FourierJacobi_Valuations_LocalMatrix
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter FourierJacobi.LocalMatrix
open FourierJacobi FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
  (μ : MeasureTheory.Measure K) [μ.IsAddHaarMeasure]

theorem FourierJacobi.Valuations.localField_matrix_minima_ae (a z : K) (ha : a ≠ 0)
    (r : ℤ) (hr : r ≠ 0) (hz : localFieldValuation K z = ((-r : ℤ) : WithTop ℤ)) :
    ∀ᵐ p : K × K ∂μ.prod μ, ∃ k j h c : ℤ,
      0 ≤ c ∧ localFieldValuation K a = (k : WithTop ℤ) ∧
      localFieldValuation K p.1 = (j : WithTop ℤ) ∧
      localFieldValuation K p.2 = (h : WithTop ℤ) ∧
      (2 * h = j - r → localFieldValuation K (p.2 ^ 2 / (p.1 * z) - 1) =
        (c : WithTop ℤ)) ∧
      matrixMinimum (localFieldValuation K) (g a p.1 p.2 z) =
        (entryMinimum r k j h : WithTop ℤ) ∧
      matrixMinimum (localFieldValuation K) (secondCompound (g a p.1 p.2 z)) =
        (minorMinimum r k j h c : WithTop ℤ) := by sorry
