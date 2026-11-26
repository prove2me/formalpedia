-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i0_upper_reindexed
-- name    : FourierJacobi.Analysis.i0_upper_reindexed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:52:12.165433+00:00
-- url     : https://prove2.me/theorems/bdf7c2bf-d1a1-5cb8-aae2-629b8ec5287b
-- title:
--   Analysis: i0 upper reindexed
-- statement:
--   The Analysis construction uses the i0 upper reindexed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L252-L282
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L252-L282

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

theorem FourierJacobi.Analysis.i0_upper_reindexed (neg : Bool) (t d U V T : ℂ) (e : Fin 2) (n : ℕ × ℕ × ℕ) :
    i0Shell t d U V T (i0UpperRowEquiv neg (e, n)).val =
      ((1 - t ^ 2) ^ 2 * i0KInitial neg t d V T * (T * V) ^ (e.val + 1) * t ^ 2) *
        (i0KRatio neg t d V T) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2.1 *
        (t ^ 2) ^ n.2.2 := by sorry
