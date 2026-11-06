-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMoment_centered_saving_of_approx
-- name    : OAI.SevenEighths.CenteredMoment.centered_saving_of_approx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:39:12.993463+00:00
-- url     : https://prove2.me/theorems/22dec7ee-36e5-4279-af70-3bb150695cf4
-- title:
--   Centered Moment: centered saving of approx
-- statement:
--   The Centered Moment construction uses the centered saving of approx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/Basic.lean#L180-L199
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/Basic.lean#L180-L199

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

theorem OAI.SevenEighths.CenteredMoment.centered_saving_of_approx
    (A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ : ℂ)
    (X₁ X₂ Y₁ Y₂ T L C E : ℝ)
    (hmain : a₁ * a₂ = b₁ * b₂)
    (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hA₁ : ‖A₁ - a₁‖ ≤ E) (hA₂ : ‖A₂ - a₂‖ ≤ E)
    (hB₁ : ‖B₁ - b₁‖ ≤ E) (hB₂ : ‖B₂ - b₂‖ ≤ E)
    (hvA₂ : ‖A₂‖ ≤ C * X₂) (hva₁ : ‖a₁‖ ≤ C * X₁)
    (hvB₂ : ‖B₂‖ ≤ C * Y₂) (hvb₁ : ‖b₁‖ ≤ C * Y₁)
    (hL : 0 < L) (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂)
    (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    ‖A₁ * A₂ - B₁ * B₂‖ ≤ 4 * E * C * (T / L) := by sorry
