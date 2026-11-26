-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i0_case1_reindexed
-- name    : FourierJacobi.Analysis.i0_case1_reindexed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:49:05.735197+00:00
-- url     : https://prove2.me/theorems/6c5427d8-f50d-5316-ad5c-debc948ca885
-- title:
--   Analysis: i0 case1 reindexed
-- statement:
--   The Analysis construction uses the i0 case1 reindexed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L111-L124
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L111-L124

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

theorem FourierJacobi.Analysis.i0_case1_reindexed (t d U V T : ℂ) (n : ℕ × ℕ × ℕ) :
    i0Shell t d U V T (i0PositiveRowEquiv false n).val =
      (1 - t ^ 2) ^ 2 * (d * T * V * t) ^ n.1 *
        (t ^ 2) ^ n.2.1 * (t ^ 2) ^ n.2.2 := by sorry
