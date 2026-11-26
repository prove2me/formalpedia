-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i0_case2_reindexed
-- name    : FourierJacobi.Analysis.i0_case2_reindexed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:50:51.425344+00:00
-- url     : https://prove2.me/theorems/df478f3a-fe48-4fcd-a0c1-bd93c2dc2272
-- title:
--   Analysis: i0 case2 reindexed
-- statement:
--   The Analysis construction uses the i0 case2 reindexed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L126-L140
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L126-L140

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

theorem FourierJacobi.Analysis.i0_case2_reindexed (t d U V T : ℂ) (n : ℕ × ℕ × ℕ) :
    i0Shell t d U V T (i0PositiveRowEquiv true n).val =
      ((1 - t ^ 2) ^ 2 * (T * U * t ^ 4)) *
        (d * T * V * t) ^ n.1 * (t ^ 2) ^ n.2.1 *
          (T * U * t ^ 4) ^ n.2.2 := by sorry
