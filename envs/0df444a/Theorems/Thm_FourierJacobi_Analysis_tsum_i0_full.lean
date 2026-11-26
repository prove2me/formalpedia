-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_tsum_i0_full
-- name    : FourierJacobi.Analysis.tsum_i0_full
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:15:15.730841+00:00
-- url     : https://prove2.me/theorems/e2c20fd4-7f76-40d0-820d-671cf66a9e82
-- title:
--   Analysis: tsum i0 full
-- statement:
--   The Analysis construction uses the tsum i0 full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L574-L580
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L574-L580

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

theorem FourierJacobi.Analysis.tsum_i0_full (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hP : ‖d * T * V * t‖ < 1)
    (hN : ‖T * V * t / d‖ < 1) (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (hF : ‖T * U * t ^ 2‖ < 1) (hG : ‖T * U * t ^ 4‖ < 1) :
    (∑' p : ℤ × ℤ × ℤ, i0Shell t d U V T p) =
      ∑ i : Fin 10, Algebra.regionTerms t d (T * U) (T * V) (i.castLE (by decide)) := by sorry
