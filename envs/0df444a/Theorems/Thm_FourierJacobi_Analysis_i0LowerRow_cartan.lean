-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i0LowerRow_cartan
-- name    : FourierJacobi.Analysis.i0LowerRow_cartan
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:59:32.294014+00:00
-- url     : https://prove2.me/theorems/d4a3f122-a9b2-5d85-b98d-07127e8fb4e8
-- title:
--   Analysis: i0 Lower Row cartan
-- statement:
--   The Analysis construction uses the i0 Lower Row cartan property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L168-L174
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L168-L174

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

theorem FourierJacobi.Analysis.i0LowerRow_cartan (neg : Bool) (n : ℕ × ℕ × ℕ) :
    cartanIndices 0 (i0LowerRowEquiv neg n).val.1
      (i0LowerRowEquiv neg n).val.2.1 (i0LowerRowEquiv neg n).val.2.2 0 =
      (2 * (n.2.1 : ℤ) + 2 * n.2.2 + 4, if neg then (n.1 : ℤ) + 1 else n.1) := by sorry
