-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_fullCorrelation_swap
-- name    : OAI.SevenEighths.CenteredMomentCorrelation.fullCorrelation_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:44:11.304226+00:00
-- url     : https://prove2.me/theorems/1859a152-a3c7-4bb8-a6c0-e5290bd11516
-- title:
--   Centered Moment Correlation: full Correlation swap
-- statement:
--   The Centered Moment Correlation construction uses the full Correlation swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/Correlation.lean#L23-L37
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/Correlation.lean#L23-L37

import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.GroupTheory.Index
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
set_option autoImplicit false
open OAI
open scoped BigOperators Classical
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {R X Y : Type*} [CommRing R] [Fintype R] [Fintype X] [Fintype Y]
omit [Fintype R]

theorem OAI.SevenEighths.CenteredMomentCorrelation.fullCorrelation_swap (left : X → R) (right : Y → R)
    (f : X → ℂ) (g : Y → ℂ) (j : R) :
    fullCorrelation left right f g j = star (fullCorrelation right left g f (-j)) := by sorry
