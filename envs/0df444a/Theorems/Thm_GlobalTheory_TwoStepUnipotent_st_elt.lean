-- Prove2me | Theorems.Thm_GlobalTheory_TwoStepUnipotent_st_elt
-- name    : GlobalTheory.TwoStepUnipotent.st_elt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:16:27.589924+00:00
-- url     : https://prove2.me/theorems/5be17754-5db6-4cd8-b26e-51e74aadd533
-- title:
--   Two Step Unipotent: st elt
-- statement:
--   The Two Step Unipotent construction uses the st elt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/TwoStepUnipotentCompactModSubring.lean#L90-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/TwoStepUnipotentCompactModSubring.lean#L90-L96

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

theorem GlobalTheory.TwoStepUnipotent.st_elt (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (hh : h + h = 1) (hc : ∀ x, h * x = x * h) (b : S) {w : S} (hw : st w = -w) :
    st (elt st h b w) = elt st h (-b) (-w) := by sorry
