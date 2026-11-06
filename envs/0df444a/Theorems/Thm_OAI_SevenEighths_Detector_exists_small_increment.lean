-- Prove2me | Theorems.Thm_OAI_SevenEighths_Detector_exists_small_increment
-- name    : OAI.SevenEighths.Detector.exists_small_increment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:23:13.192329+00:00
-- url     : https://prove2.me/theorems/bd7b9784-d5ad-4b15-9467-3b5d6f4190e1
-- title:
--   Detector: exists small increment
-- statement:
--   The Detector construction uses the exists small increment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector.lean#L13-L24
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector.lean#L13-L24

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Detector

theorem OAI.SevenEighths.Detector.exists_small_increment (M : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    {lo hi e : ℝ} (hlo : lo ≤ M 0) (hhi : M n ≤ hi)
    (hwidth : hi - lo ≤ n * e) :
    ∃ i < n, M (i + 1) - M i ≤ e := by sorry
