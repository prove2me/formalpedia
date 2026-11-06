-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_fullCorrelation_reduction_unit_left
-- name    : OAI.SevenEighths.CenteredMomentCorrelation.fullCorrelation_reduction_unit_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:44:26.976192+00:00
-- url     : https://prove2.me/theorems/a58c85bd-88bc-4656-95f1-0e2cb65eeb58
-- title:
--   Centered Moment Correlation: full Correlation reduction unit left
-- statement:
--   The Centered Moment Correlation construction uses the full Correlation reduction unit left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/Correlation.lean#L278-L287
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/Correlation.lean#L278-L287

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

theorem OAI.SevenEighths.CenteredMomentCorrelation.fullCorrelation_reduction_unit_left (π : A →+* B)
    (hπ : Function.Surjective π) (u : A) (v : Aˣ) (k : A) (f g : B → ℂ) :
    fullCorrelation (fun x : A => (v : A) * x) (fun y : A => u * y)
        (fun x => f (π x)) (fun y => g (π y)) k =
      (reductionMultiplicity π : ℂ) *
        fullCorrelation (fun x : B => π v * x) (fun y : B => π u * y) f g (π k) := by sorry
