-- Prove2me | Theorems.Thm_GlobalTheory_TwoStepUnipotent_mul_aux
-- name    : GlobalTheory.TwoStepUnipotent.mul_aux
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:16:28.548715+00:00
-- url     : https://prove2.me/theorems/1225b3dd-f730-4d42-ada4-9939bb3a5630
-- title:
--   Two Step Unipotent: mul aux
-- statement:
--   The Two Step Unipotent construction uses the mul aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/TwoStepUnipotentCompactModSubring.lean#L30-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/TwoStepUnipotentCompactModSubring.lean#L30-L63

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

theorem GlobalTheory.TwoStepUnipotent.mul_aux {b c z b' c' z' : S} (h31 : e₃ * e₁ = 0)
    (h1 : b * e₃ = b) (h2 : z * e₃ = z) (h3 : e₃ * b' = 0) (h4 : e₁ * c' = c')
    (h5 : e₁ * z' = z') (h6 : c * e₁ = 0) :
    (1 - c + b + z) * (1 - c' + b' + z') = 1 - (c + c') + (b + b') + (z + z' - c * b') := by sorry
