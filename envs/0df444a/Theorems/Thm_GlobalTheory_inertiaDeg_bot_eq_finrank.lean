-- Prove2me | Theorems.Thm_GlobalTheory_inertiaDeg_bot_eq_finrank
-- name    : GlobalTheory.inertiaDeg_bot_eq_finrank
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:55:15.916188+00:00
-- url     : https://prove2.me/theorems/b0682dd1-7d11-49ce-96d8-5cba24501d3b
-- title:
--   Global Theory: inertia Deg bot eq finrank
-- statement:
--   The Global Theory construction uses the inertia Deg bot eq finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InertiaDegBotEqFinrankFiniteDomain.lean#L5-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InertiaDegBotEqFinrankFiniteDomain.lean#L5-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertiaDegBotEqFinrankFiniteDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.inertiaDeg_bot_eq_finrank : ∀ (R S : Type) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S], Function.Injective (algebraMap R S) → (⊥ : Ideal S).inertiaDeg R = Module.finrank R S := by sorry
