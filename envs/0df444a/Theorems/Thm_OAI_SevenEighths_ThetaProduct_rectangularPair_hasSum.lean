-- Prove2me | Theorems.Thm_OAI_SevenEighths_ThetaProduct_rectangularPair_hasSum
-- name    : OAI.SevenEighths.ThetaProduct.rectangularPair_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:53:19.998804+00:00
-- url     : https://prove2.me/theorems/d7691e53-29db-434d-8407-7203ee9bff0e
-- title:
--   Theta Product: rectangular Pair has Sum
-- statement:
--   The Theta Product construction uses the rectangular Pair has Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ThetaProduct.lean#L139-L158
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ThetaProduct.lean#L139-L158

import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_ThetaProduct
set_option autoImplicit false
open OAI
noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology
open OAI.SevenEighths OAI.SevenEighths.ThetaProduct

theorem OAI.SevenEighths.ThetaProduct.rectangularPair_hasSum (a b u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ × ℤ =>
      (Real.exp (-Real.pi * (u * (n.1 + a) ^ 2 + v * (n.2 + b) ^ 2) * t) : ℂ))
      ((rectangularPair a b u v hu hv).f t) := by sorry
