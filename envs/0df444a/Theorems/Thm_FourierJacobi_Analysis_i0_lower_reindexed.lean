-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i0_lower_reindexed
-- name    : FourierJacobi.Analysis.i0_lower_reindexed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:51:56.180361+00:00
-- url     : https://prove2.me/theorems/f9b0f9aa-4e16-420e-9a20-545525bc013c
-- title:
--   Analysis: i0 lower reindexed
-- statement:
--   The Analysis construction uses the i0 lower reindexed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L221-L250
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L221-L250

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_FourierJacobi_Analysis_I0Complete
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

theorem FourierJacobi.Analysis.i0_lower_reindexed (neg : Bool) (t d U V T : ℂ) (n : ℕ × ℕ × ℕ) :
    i0Shell t d U V T (i0LowerRowEquiv neg n).val =
      ((1 - t ^ 2) ^ 2 * i0KInitial neg t d V T * (T * U * t ^ 2) *
        (T * U * t ^ 4)) * (i0KRatio neg t d V T) ^ n.1 *
        (T * U * t ^ 2) ^ n.2.1 * (T * U * t ^ 4) ^ n.2.2 := by sorry
