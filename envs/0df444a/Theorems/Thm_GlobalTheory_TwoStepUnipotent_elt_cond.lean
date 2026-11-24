-- Prove2me | Theorems.Thm_GlobalTheory_TwoStepUnipotent_elt_cond
-- name    : GlobalTheory.TwoStepUnipotent.elt_cond
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:16:42.502804+00:00
-- url     : https://prove2.me/theorems/3d887893-b6f4-47a9-b40b-e74dfdc0f732
-- title:
--   Two Step Unipotent: elt cond
-- statement:
--   The Two Step Unipotent construction uses the elt cond property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/TwoStepUnipotentCompactModSubring.lean#L114-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/TwoStepUnipotentCompactModSubring.lean#L114-L143

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_TwoStepUnipotentCompactModSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory GlobalTheory.TwoStepUnipotent
variable {S : Type} [Ring S] (st : S →+ S) (e₁ e₃ h : S)
variable {st e₁ e₃ h}

theorem GlobalTheory.TwoStepUnipotent.elt_cond (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (hs : st e₁ = e₃) (h31 : e₃ * e₁ = 0) (hh : h + h = 1) (hc : ∀ x, h * x = x * h)
    {b w : S} (hb : e₁ * b = 0 ∧ e₃ * b = 0 ∧ b * e₃ = b)
    (hw : e₁ * w = w ∧ w * e₃ = w ∧ st w = -w) :
    st (elt st h b w) * elt st h b w = 1 ∧ (elt st h b w - 1) * e₁ = 0 ∧
      (1 - e₁) * (elt st h b w - 1) * (1 - e₃) = 0 := by sorry
