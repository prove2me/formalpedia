-- Prove2me | Theorems.Thm_GlobalTheory_FibrePowerProper_isProper_fan_pt
-- name    : GlobalTheory.FibrePowerProper.isProper_fan_pt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:24:35.029808+00:00
-- url     : https://prove2.me/theorems/2d9bc9b8-4a72-44b2-8d64-4dab43f5db2a
-- title:
--   Fibre Power Proper: is Proper fan pt
-- statement:
--   The Fibre Power Proper construction uses the is Proper fan pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsProperEighthFibrePowerOver.lean#L22-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsProperEighthFibrePowerOver.lean#L22-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsProperEighthFibrePowerOver
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.FibrePowerProper

theorem GlobalTheory.FibrePowerProper.isProper_fan_pt {T : Scheme.{0}} : ∀ (n : ℕ) (f : Fin n → Over T),
    (∀ i, IsProper (f i).hom) → ∀ (c : Fan f), IsLimit c → IsProper c.pt.hom
  := by sorry
