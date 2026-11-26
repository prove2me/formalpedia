-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_case1_regionTerm
-- name    : FourierJacobi.Analysis.hasSum_i0_case1_regionTerm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:58:45.251988+00:00
-- url     : https://prove2.me/theorems/fa35d7ff-69fe-43c1-8e89-ee78176f22f3
-- title:
--   Analysis: has Sum i0 case1 region Term
-- statement:
--   Direct identification with row 0 of the existing fifty-row expression,
--   under the expansion's damping substitution `U ↦ TU`, `V ↦ TV`.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L395-L403
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean#L395-L403

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

theorem FourierJacobi.Analysis.hasSum_i0_case1_regionTerm (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hP : ‖d * T * V * t‖ < 1) :
    HasSum (fun p : I0PositiveRow false => i0Shell t d U V T p.val)
      (Algebra.regionTerm0 t d (T * U) (T * V)
        (1 - d * (T * V) * t) (1 - (T * V) * t / d)
        (1 - (T * V) ^ 2 * t ^ 2) (1 - (T * U) * t ^ 2)
        (1 - (T * U) * t ^ 4)) := by sorry
