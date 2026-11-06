-- Prove2me | Theorems.Thm_OAI_SevenEighths_PNT_retained_ratio_tendsto
-- name    : OAI.SevenEighths.PNT.retained_ratio_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:23:30.493641+00:00
-- url     : https://prove2.me/theorems/5b1fd5e1-76ae-4352-88a0-4a2d98863644
-- title:
--   PNT: retained ratio tendsto
-- statement:
--   The PNT construction uses the retained ratio tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeCounting/PrimeMass.lean#L44-L64
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeCounting/PrimeMass.lean#L44-L64

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeCounting_Progressions
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeCounting_PrimeMass
import Theorems.Thm_W21_hf

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.PNT
open Filter ArithmeticFunction
open scoped Topology BigOperators

theorem OAI.SevenEighths.PNT.retained_ratio_tendsto {f : ℕ → ℝ} {A : ℝ} (keep : ℕ → Prop)
    [DecidablePred keep] (hf : ∀ n, 0 ≤ f n) (hzero : f 0 = 0)
    (hmass : Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 A))
    (hremainder : Summable (fun n => (if keep n then 0 else f n) / n)) :
    Tendsto (fun N : ℕ => cumsum (fun n => if keep n then f n else 0) N / N)
      atTop (𝓝 A) := by sorry
