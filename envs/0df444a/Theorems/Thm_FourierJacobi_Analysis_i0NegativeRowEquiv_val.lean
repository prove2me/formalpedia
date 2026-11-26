-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
-- name    : FourierJacobi.Analysis.i0NegativeRowEquiv_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:48:58.894748+00:00
-- url     : https://prove2.me/theorems/0f3b015a-1bf2-5caa-b9eb-5ca8ff81d2d9
-- title:
--   Analysis: i0 Negative Row Equiv val
-- statement:
--   The Analysis construction uses the i0 Negative Row Equiv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L273-L275
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L273-L275

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000

theorem FourierJacobi.Analysis.i0NegativeRowEquiv_val (tail : Bool) (n : ℕ × ℕ × ℕ) :
    (i0NegativeRowEquiv tail n).val = (-(n.1 : ℤ) - 1, (n.2.1 : ℤ),
      if tail then -(n.2.2 : ℤ) - 1 else (n.2.2 : ℤ)) := by sorry

attribute [defeq] FourierJacobi.Analysis.i0NegativeRowEquiv_val
