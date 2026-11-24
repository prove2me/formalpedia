-- Prove2me | Theorems.Thm_GlobalTheory_FibrePowerProper_isProper_eighth_fibre_power
-- name    : GlobalTheory.FibrePowerProper.isProper_eighth_fibre_power
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:24:30.886342+00:00
-- url     : https://prove2.me/theorems/1f1878ba-fbc2-4e56-87d6-0cbeedeca531
-- title:
--   Fibre Power Proper: is Proper eighth fibre power
-- statement:
--   The Fibre Power Proper construction uses the is Proper eighth fibre power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsProperEighthFibrePowerOver.lean#L37-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsProperEighthFibrePowerOver.lean#L37-L45

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

theorem GlobalTheory.FibrePowerProper.isProper_eighth_fibre_power : ∀ {T : Scheme.{0}} {B C : Over T} (pr : Fin 8 → (B ⟶ C)),
    (∀ (T' : Over T) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr a = y a) →
    IsProper C.hom → IsProper B.hom := by sorry
