-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i0Region_partition
-- name    : FourierJacobi.Analysis.i0Region_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:54:14.623399+00:00
-- url     : https://prove2.me/theorems/f9ca035a-b0c3-4e17-aae0-2a5d668e9a0c
-- title:
--   Analysis: i0 Region partition
-- statement:
--   The Analysis construction uses the i0 Region partition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L509-L511
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L509-L511

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

theorem FourierJacobi.Analysis.i0Region_partition (p : ℤ × ℤ × ℤ) : ∃! i : Fin 10, p ∈ i0Region i := by sorry
