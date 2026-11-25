-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_EpsProj_eps_mul
-- name    : GlobalTheory.BadShare.EpsProj.eps_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:47:06.495476+00:00
-- url     : https://prove2.me/theorems/d40226e8-faf1-4e1d-95d9-d6a2dd71f828
-- title:
--   Eps Proj: eps mul
-- statement:
--   The Eps Proj construction uses the eps mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SubgroupCharacterIdempotentProperties.lean#L35-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SubgroupCharacterIdempotentProperties.lean#L35-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SubgroupCharacterIdempotentProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare GlobalTheory.BadShare.EpsProj
variable {G : Type} [Group G] [Fintype G] {S : G → Prop} {χ : G → ℂ}

theorem GlobalTheory.BadShare.EpsProj.eps_mul (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) {u : G} (hu : S u) (y : G) :
    eps S χ (u⁻¹ * y) = χ u * eps S χ y := by sorry
