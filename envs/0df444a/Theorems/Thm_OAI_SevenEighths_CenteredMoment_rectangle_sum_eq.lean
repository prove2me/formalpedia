-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMoment_rectangle_sum_eq
-- name    : OAI.SevenEighths.CenteredMoment.rectangle_sum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:53:06.629642+00:00
-- url     : https://prove2.me/theorems/2ea4766e-8044-4639-8861-7883784defca
-- title:
--   Centered Moment: rectangle sum eq
-- statement:
--   The Centered Moment construction uses the rectangle sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/Basic.lean#L75-L87
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/Basic.lean#L75-L87

import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Group.Commute.Units
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Basic
set_option autoImplicit false
open OAI
open scoped BigOperators NNReal
open OAI.SevenEighths OAI.SevenEighths.CenteredMoment
noncomputable section
variable {M R : Type*} [CommMonoid M] [CommRing R]

theorem OAI.SevenEighths.CenteredMoment.rectangle_sum_eq (d : MaskedCharacter M R) (N : M →* ℝ≥0) (t : ℝ)
    (s₁ s₂ : Finset M) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) :
    (∑ a ∈ s₁, ∑ b ∈ s₂,
      coefficient d N t (a * b) * rectangle N W₁ W₂ X₁ X₂ Y₁ Y₂ a b) =
      plainSum d N t s₁ W₁ X₁ * plainSum d N t s₂ W₂ X₂ -
        plainSum d N t s₁ W₁ Y₁ * plainSum d N t s₂ W₂ Y₂ := by sorry
