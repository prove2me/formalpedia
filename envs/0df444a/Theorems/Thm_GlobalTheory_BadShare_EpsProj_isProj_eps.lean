-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_EpsProj_isProj_eps
-- name    : GlobalTheory.BadShare.EpsProj.isProj_eps
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:47:27.850472+00:00
-- url     : https://prove2.me/theorems/b2037657-f264-41c3-a91b-2021858faede
-- title:
--   Eps Proj: is Proj eps
-- statement:
--   The Eps Proj construction uses the is Proj eps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SubgroupCharacterIdempotentProperties.lean#L69-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SubgroupCharacterIdempotentProperties.lean#L69-L88

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

theorem GlobalTheory.BadShare.EpsProj.isProj_eps (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) : IsProj (eps S χ) := by sorry
