-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_full
-- name    : FourierJacobi.Analysis.hasSum_i0_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:02:25.478038+00:00
-- url     : https://prove2.me/theorems/a9cc1f4f-6e6d-41d4-94a6-6fa291132484
-- title:
--   Analysis: has Sum i0 full
-- statement:
--   Complete evaluation of the independently defined zero-central-coordinate
--   valuation series. The sum on the right is exactly rows 0--9 of the stored
--   fifty-row expression, with damping inserted in the unsummed monomial.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L560-L572
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L560-L572

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

theorem FourierJacobi.Analysis.hasSum_i0_full (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hP : ‖d * T * V * t‖ < 1)
    (hN : ‖T * V * t / d‖ < 1) (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (hF : ‖T * U * t ^ 2‖ < 1) (hG : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : ℤ × ℤ × ℤ => i0Shell t d U V T p)
      (∑ i : Fin 10, Algebra.regionTerms t d (T * U) (T * V) (i.castLE (by decide))) := by sorry
