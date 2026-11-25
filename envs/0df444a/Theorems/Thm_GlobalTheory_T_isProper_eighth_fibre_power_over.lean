-- Prove2me | Theorems.Thm_GlobalTheory_T_isProper_eighth_fibre_power_over
-- name    : GlobalTheory.T.isProper_eighth_fibre_power_over
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:35:55.191016+00:00
-- url     : https://prove2.me/theorems/b10dfb40-866f-57e3-b28b-edf9339c1a2e
-- title:
--   T: is Proper eighth fibre power over
-- statement:
--   The T construction uses the is Proper eighth fibre power over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsProperEighthFibrePowerOverStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsProperEighthFibrePowerOverStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsProperEighthFibrePowerOver
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsProperEighthFibrePowerOverStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isProper_eighth_fibre_power_over : ∀ {T : Scheme.{0}} {B C : Over T} (pr : Fin 8 → (B ⟶ C)), (∀ (T' : Over T) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr a = y a) → IsProper C.hom → IsProper B.hom := by sorry
