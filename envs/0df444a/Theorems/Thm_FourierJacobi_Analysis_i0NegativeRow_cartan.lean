-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i0NegativeRow_cartan
-- name    : FourierJacobi.Analysis.i0NegativeRow_cartan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:51:11.101433+00:00
-- url     : https://prove2.me/theorems/89f73dbf-beab-41ac-a5b9-92e768a128db
-- title:
--   Analysis: i0 Negative Row cartan
-- statement:
--   The Analysis construction uses the i0 Negative Row cartan property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L277-L298
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L277-L298

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

theorem FourierJacobi.Analysis.i0NegativeRow_cartan (tail : Bool) (n : ℕ × ℕ × ℕ) :
    cartanIndices 0 (i0NegativeRowEquiv tail n).val.1
      (i0NegativeRowEquiv tail n).val.2.1
      (i0NegativeRowEquiv tail n).val.2.2 0 =
      (if tail then (2 * (n.2.2 : ℤ) + 2, (n.1 : ℤ) + 1)
        else (0, (n.1 : ℤ) + 1)) := by sorry
