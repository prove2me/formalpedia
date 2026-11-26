-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i0RegionIndex_mem
-- name    : FourierJacobi.Analysis.i0RegionIndex_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:00:41.98436+00:00
-- url     : https://prove2.me/theorems/ee61cb51-6ee4-4bbc-b81d-95176e4a6601
-- title:
--   Analysis: i0 Region Index mem
-- statement:
--   The Analysis construction uses the i0 Region Index mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L499-L501
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L499-L501

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

theorem FourierJacobi.Analysis.i0RegionIndex_mem (p : ℤ × ℤ × ℤ) : p ∈ i0Region (i0RegionIndex p) := by sorry
