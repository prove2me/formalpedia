-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_middle
-- name    : FourierJacobi.Analysis.hasSum_i0_middle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:51:59.267339+00:00
-- url     : https://prove2.me/theorems/ddae9699-83f8-58df-ad37-da31e17175c5
-- title:
--   Analysis: has Sum i0 middle
-- statement:
--   The Analysis construction uses the has Sum i0 middle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L300-L311
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L300-L311

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

theorem FourierJacobi.Analysis.hasSum_i0_middle (neg : Bool) (t d U V T : ℂ)
    (hK : ‖i0KRatio neg t d V T‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) (hF : ‖T * U * t ^ 2‖ < 1) :
    HasSum (fun p : I0MiddleRow neg => i0Shell t d U V T p.val)
      (((1 - t ^ 2) ^ 2 * i0KInitial neg t d V T * (T * U * t ^ 2)) *
        (1 - i0KRatio neg t d V T)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ *
        (1 - T * U * t ^ 2)⁻¹) := by sorry
