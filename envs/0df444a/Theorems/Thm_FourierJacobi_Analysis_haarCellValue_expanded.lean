-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_haarCellValue_expanded
-- name    : FourierJacobi.Analysis.haarCellValue_expanded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:39:16.828872+00:00
-- url     : https://prove2.me/theorems/837d9a67-fdd1-5262-8b77-5b6d9fc9ef1c
-- title:
--   Analysis: haar Cell Value expanded
-- statement:
--   The Analysis construction uses the haar Cell Value expanded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellValue.lean#L65-L88
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellValue.lean#L65-L88

import Definitions.Def_FourierJacobi_Analysis_HaarLatticePartition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_HaarCellValue
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
set_option maxHeartbeats 2000000

theorem FourierJacobi.Analysis.haarCellValue_expanded (q : ℝ) (hq : 0 < q) (a b d : ℂ)
    (T : ℝ) (hT : T ≠ 0) (r : ℤ) (i : LatticeIndex) :
    haarCellValue q a b d T r i =
      d ^ i.1 * (inverseSqrt q : ℂ) ^ (3 * i.1) *
        ((poincare (inverseSqrt q : ℂ))⁻¹ * ∑ w : Fin 8,
          weylWeights (inverseSqrt q : ℂ) a b w *
            (inverseSqrt q : ℂ) ^
              (3 * (cartanIndices r i.1 i.2.1 i.2.2.1 i.2.2.2).1 +
                4 * (cartanIndices r i.1 i.2.1 i.2.2.1 i.2.2.2).2) *
            ((T : ℂ) * weylU a b w) ^
              ((cartanIndices r i.1 i.2.1 i.2.2.1 i.2.2.2).1 / 2) *
            ((T : ℂ) * weylV a b w) ^
              (cartanIndices r i.1 i.2.1 i.2.2.1 i.2.2.2).2) := by sorry
