-- Prove2me | Theorems.Thm_GlobalTheory_TwoStepUnipotent_elt_neg_mul
-- name    : GlobalTheory.TwoStepUnipotent.elt_neg_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:22.924602+00:00
-- url     : https://prove2.me/theorems/a01748af-321b-498b-8b6e-f97f116cc5d9
-- title:
--   Two Step Unipotent: elt neg mul
-- statement:
--   The Two Step Unipotent construction uses the elt neg mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/TwoStepUnipotentCompactModSubring.lean#L98-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/TwoStepUnipotentCompactModSubring.lean#L98-L104

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

theorem GlobalTheory.TwoStepUnipotent.elt_neg_mul (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (hs : st e₁ = e₃) (h31 : e₃ * e₁ = 0) (hh : h + h = 1) (hc : ∀ x, h * x = x * h)
    {b w : S} (hb : e₃ * b = 0 ∧ b * e₃ = b) (hw : e₁ * w = w ∧ w * e₃ = w) :
    elt st h (-b) (-w) * elt st h b w = 1 := by sorry
