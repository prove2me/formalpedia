-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_summable_norm_i0_upper_reindexed
-- name    : FourierJacobi.Analysis.summable_norm_i0_upper_reindexed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:52:31.400314+00:00
-- url     : https://prove2.me/theorems/354a5b80-bf94-4495-b607-d8b0498cc499
-- title:
--   Analysis: summable norm i0 upper reindexed
-- statement:
--   The Analysis construction uses the summable norm i0 upper reindexed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L335-L346
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L335-L346

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

theorem FourierJacobi.Analysis.summable_norm_i0_upper_reindexed (neg : Bool) (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hK : ‖i0KRatio neg t d V T‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun n : Fin 2 × ℕ × ℕ × ℕ =>
      ‖i0Shell t d U V T (i0UpperRowEquiv neg n).val‖) := by sorry
