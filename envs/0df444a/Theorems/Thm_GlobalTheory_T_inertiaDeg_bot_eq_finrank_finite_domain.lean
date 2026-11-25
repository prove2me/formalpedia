-- Prove2me | Theorems.Thm_GlobalTheory_T_inertiaDeg_bot_eq_finrank_finite_domain
-- name    : GlobalTheory.T.inertiaDeg_bot_eq_finrank_finite_domain
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:18.232844+00:00
-- url     : https://prove2.me/theorems/19da97f0-a493-45bd-877b-3dfc9afbd0c6
-- title:
--   T: inertia Deg bot eq finrank finite domain
-- statement:
--   The T construction uses the inertia Deg bot eq finrank finite domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InertiaDegBotEqFinrankFiniteDomainStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InertiaDegBotEqFinrankFiniteDomainStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertiaDegBotEqFinrankFiniteDomain
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertiaDegBotEqFinrankFiniteDomainStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.inertiaDeg_bot_eq_finrank_finite_domain : ∀ (R S : Type) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S], Function.Injective (algebraMap R S) → (⊥ : Ideal S).inertiaDeg R = Module.finrank R S := by sorry
