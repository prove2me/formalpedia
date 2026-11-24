-- Prove2me | Theorems.Thm_GlobalTheory_TwoStepUnipotent_elt_mul
-- name    : GlobalTheory.TwoStepUnipotent.elt_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:24:34.565037+00:00
-- url     : https://prove2.me/theorems/8ca04143-3e12-49cc-8e0a-3f33dcd723d2
-- title:
--   Two Step Unipotent: elt mul
-- statement:
--   The Two Step Unipotent construction uses the elt mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/TwoStepUnipotentCompactModSubring.lean#L65-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/TwoStepUnipotentCompactModSubring.lean#L65-L88

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

theorem GlobalTheory.TwoStepUnipotent.elt_mul (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (hs : st e₁ = e₃) (h31 : e₃ * e₁ = 0) (hh : h + h = 1) (hc : ∀ x, h * x = x * h)
    {b w b' w' : S} (hb : e₃ * b = 0 ∧ b * e₃ = b) (hb' : e₃ * b' = 0 ∧ b' * e₃ = b')
    (hw : w * e₃ = w) (hw' : e₁ * w' = w') :
    elt st h b w * elt st h b' w'
      = elt st h (b + b') (w + w' + h * (st b' * b - st b * b')) := by sorry
