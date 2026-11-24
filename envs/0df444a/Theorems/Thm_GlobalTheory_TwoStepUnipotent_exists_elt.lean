-- Prove2me | Theorems.Thm_GlobalTheory_TwoStepUnipotent_exists_elt
-- name    : GlobalTheory.TwoStepUnipotent.exists_elt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:12:05.316722+00:00
-- url     : https://prove2.me/theorems/ac4fbfe7-8e12-4253-a4b7-738db9072aef
-- title:
--   Two Step Unipotent: exists elt
-- statement:
--   The Two Step Unipotent construction uses the exists elt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/TwoStepUnipotentCompactModSubring.lean#L145-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/TwoStepUnipotentCompactModSubring.lean#L145-L222

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

theorem GlobalTheory.TwoStepUnipotent.exists_elt (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (h11 : e₁ * e₁ = e₁)
    (hs : st e₁ = e₃) (h31 : e₃ * e₁ = 0) (hh : h + h = 1) (hc : ∀ x, h * x = x * h)
    {g : S} (h1 : st g * g = 1) (h2 : (g - 1) * e₁ = 0)
    (h3 : (1 - e₁) * (g - 1) * (1 - e₃) = 0) :
    ∃ b w, (e₁ * b = 0 ∧ e₃ * b = 0 ∧ b * e₃ = b) ∧ (e₁ * w = w ∧ w * e₃ = w ∧ st w = -w) ∧
      g = elt st h b w := by sorry
