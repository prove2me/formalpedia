-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i0PositiveRow_cartan
-- name    : FourierJacobi.Analysis.i0PositiveRow_cartan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:49:58.620985+00:00
-- url     : https://prove2.me/theorems/7ed52125-52cb-40fd-ba16-652733a57fd3
-- title:
--   Analysis: i0 Positive Row cartan
-- statement:
--   The Analysis construction uses the i0 Positive Row cartan property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L91-L109
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L91-L109

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

theorem FourierJacobi.Analysis.i0PositiveRow_cartan (tail : Bool) (n : ℕ × ℕ × ℕ) :
    cartanIndices 0 (i0PositiveRowEquiv tail n).val.1
      (i0PositiveRowEquiv tail n).val.2.1
      (i0PositiveRowEquiv tail n).val.2.2 0 =
      (if tail then (2 * (n.2.2 : ℤ) + 2, (n.1 : ℤ)) else (0, (n.1 : ℤ))) := by sorry
