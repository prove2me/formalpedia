-- Prove2me | Theorems.Thm_OAI_SevenEighths_PNT_cumsum_div_tendsto_zero_of_summable_div
-- name    : OAI.SevenEighths.PNT.cumsum_div_tendsto_zero_of_summable_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:23:27.505683+00:00
-- url     : https://prove2.me/theorems/7070162a-ea20-4d36-a163-c8a9945ecf3e
-- title:
--   PNT: cumsum div tendsto zero of summable div
-- statement:
--   The PNT construction uses the cumsum div tendsto zero of summable div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeCounting/PrimeMass.lean#L10-L42
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeCounting/PrimeMass.lean#L10-L42

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeCounting_Progressions
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeCounting_PrimeMass
import Theorems.Thm_W21_hf

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.PNT
open Filter ArithmeticFunction
open scoped Topology BigOperators

theorem OAI.SevenEighths.PNT.cumsum_div_tendsto_zero_of_summable_div {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hzero : f 0 = 0)
    (hsum : Summable (fun n => f n / n)) :
    Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 0) := by sorry
