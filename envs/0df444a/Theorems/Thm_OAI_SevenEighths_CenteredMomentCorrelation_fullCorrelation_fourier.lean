-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_fullCorrelation_fourier
-- name    : OAI.SevenEighths.CenteredMomentCorrelation.fullCorrelation_fourier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:44:11.845483+00:00
-- url     : https://prove2.me/theorems/58ebf138-39c4-492b-8b2b-eec4ae5b9664
-- title:
--   Centered Moment Correlation: full Correlation fourier
-- statement:
--   The Centered Moment Correlation construction uses the full Correlation fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/Correlation.lean#L39-L72
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/Correlation.lean#L39-L72

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

theorem OAI.SevenEighths.CenteredMomentCorrelation.fullCorrelation_fourier (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (left : X → R) (right : Y → R) (f : X → ℂ) (g : Y → ℂ) (j : R) :
    (∑ h : R, fourierSum ψ left f h * star (fourierSum ψ right g h) * ψ (-(h * j))) =
      (Fintype.card R : ℂ) * fullCorrelation left right f g j := by sorry
