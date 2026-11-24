-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_Red_card_eq
-- name    : GlobalTheory.LatPair.Red.card_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:59:52.036575+00:00
-- url     : https://prove2.me/theorems/1f1e027d-203a-4d20-9a9b-aeef8a7536e8
-- title:
--   Red: card eq
-- statement:
--   The Red construction uses the card eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L369-L371
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L369-L371

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
variable {n n' : Type*}
open GlobalTheory.LatPair.Red
variable (L : Submodule 𝒪[k] (n → k))
variable {L}

theorem GlobalTheory.LatPair.Red.card_eq [Fintype n] [L.IsLattice k] : Nat.card (Red L) = SplitWeil.resCard k ^ Fintype.card n := by sorry
