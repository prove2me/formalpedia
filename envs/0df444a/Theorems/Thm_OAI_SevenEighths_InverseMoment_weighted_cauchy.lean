-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_weighted_cauchy
-- name    : OAI.SevenEighths.InverseMoment.weighted_cauchy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:24:10.843776+00:00
-- url     : https://prove2.me/theorems/f517a0e8-2508-4a5b-aed8-2b554efaaa50
-- title:
--   Inverse Moment: weighted cauchy
-- statement:
--   The Inverse Moment construction uses the weighted cauchy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/Fibers.lean#L21-L48
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/Fibers.lean#L21-L48

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Fibers
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators
noncomputable section

theorem OAI.SevenEighths.InverseMoment.weighted_cauchy {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (f g : ι → ℂ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    ‖∑ i ∈ s, (w i : ℂ) * f i * star (g i)‖ ≤
      Real.sqrt (weightedEnergy s w f) * Real.sqrt (weightedEnergy s w g) := by sorry
