-- Prove2me | Theorems.Thm_OAI_AnalyticBridge_reassembled_bilinear_bound
-- name    : OAI.AnalyticBridge.reassembled_bilinear_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:29:08.772199+00:00
-- url     : https://prove2.me/theorems/45f01fda-fba6-4f66-aba0-e25f4f29da91
-- title:
--   Analytic Bridge: reassembled bilinear bound
-- statement:
--   The Analytic Bridge construction uses the reassembled bilinear bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/ExponentialSmoothing.lean#L66-L98
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/ExponentialSmoothing.lean#L66-L98

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open OAI.AnalyticBridge
variable {Ω : Type*}

theorem OAI.AnalyticBridge.reassembled_bilinear_bound
    {Λ₁ Λ₂ : Type*} [DecidableEq Λ₁] [DecidableEq Λ₂]
    (S : Finset Ω) (T₁ : Finset Λ₁) (T₂ : Finset Λ₂)
    (label₁ : Ω → Λ₁) (label₂ : Ω → Λ₂)
    (w : Ω → ℂ) (A : Λ₁ → ℂ) (B : Λ₂ → ℂ)
    (M₁ M₂ : ℝ)
    (hM₁ : 0 ≤ M₁)
    (hmap₁ : ∀ ω ∈ S, label₁ ω ∈ T₁)
    (hmap₂ : ∀ ω ∈ S, label₂ ω ∈ T₂)
    (hfiber₁ : ∀ a ∈ T₁,
      (∑ ω ∈ S with label₁ ω = a, ‖w ω‖) ≤ M₁)
    (hfiber₂ : ∀ a ∈ T₂,
      (∑ ω ∈ S with label₂ ω = a, ‖w ω‖) ≤ M₂) :
    ‖∑ ω ∈ S, w ω * A (label₁ ω) * star (B (label₂ ω))‖ ^ 2 ≤
      (M₁ * ∑ a ∈ T₁, ‖A a‖ ^ 2) *
        (M₂ * ∑ a ∈ T₂, ‖B a‖ ^ 2) := by sorry
