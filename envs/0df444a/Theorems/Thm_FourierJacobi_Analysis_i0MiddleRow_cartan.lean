-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i0MiddleRow_cartan
-- name    : FourierJacobi.Analysis.i0MiddleRow_cartan
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:59:25.326797+00:00
-- url     : https://prove2.me/theorems/d47c5b7f-4046-5e89-9e2e-70fb4bc06aeb
-- title:
--   Analysis: i0 Middle Row cartan
-- statement:
--   The Analysis construction uses the i0 Middle Row cartan property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L160-L166
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean#L160-L166

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

theorem FourierJacobi.Analysis.i0MiddleRow_cartan (neg : Bool) (n : ℕ × ℕ × ℕ) :
    cartanIndices 0 (i0MiddleRowEquiv neg n).val.1
      (i0MiddleRowEquiv neg n).val.2.1 (i0MiddleRowEquiv neg n).val.2.2 0 =
      (2 * (n.2.2 : ℤ) + 2, (if neg then (n.1 : ℤ) + 1 else n.1) + 2 * n.2.1) := by sorry
