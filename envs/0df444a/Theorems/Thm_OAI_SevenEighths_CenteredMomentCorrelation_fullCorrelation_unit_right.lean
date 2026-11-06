-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_fullCorrelation_unit_right
-- name    : OAI.SevenEighths.CenteredMomentCorrelation.fullCorrelation_unit_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:44:30.831288+00:00
-- url     : https://prove2.me/theorems/03c28259-5a92-4518-b513-881a5be4ebaa
-- title:
--   Centered Moment Correlation: full Correlation unit right
-- statement:
--   The Centered Moment Correlation construction uses the full Correlation unit right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/Correlation.lean#L247-L260
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/Correlation.lean#L247-L260

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
variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]

theorem OAI.SevenEighths.CenteredMomentCorrelation.fullCorrelation_unit_right (u : Aˣ) (v k : A) (f g : A → ℂ) :
    fullCorrelation (fun x => v * x) (fun y => (u : A) * y) f g k =
      ∑ x : A, f x * star (g ((↑u⁻¹ : A) * (v * x - k))) := by sorry
