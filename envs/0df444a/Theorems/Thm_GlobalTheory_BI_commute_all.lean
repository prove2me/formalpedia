-- Prove2me | Theorems.Thm_GlobalTheory_BI_commute_all
-- name    : GlobalTheory.BI.commute_all
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:20:59.286986+00:00
-- url     : https://prove2.me/theorems/9200abb4-f1a4-4b25-98e6-02e072f1bf00
-- title:
--   BI: commute all
-- statement:
--   The BI construction uses the commute all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CommuteImageAbelianByPrimePowerOfNormalCentral.lean#L6-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CommuteImageAbelianByPrimePowerOfNormalCentral.lean#L6-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CommuteImageAbelianByPrimePowerOfNormalCentral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
open GlobalTheory GlobalTheory.BI

theorem GlobalTheory.BI.commute_all : ∀ (G : Type) [Group G] [Finite G] (M : Type) [Monoid M] (φ : G →* M), _root_.GlobalTheory.BI.AbByP G → (∀ B : Subgroup G, B.Normal → (∀ a ∈ B, ∀ b ∈ B, φ a * φ b = φ b * φ a) → ∀ b ∈ B, ∀ g : G, φ b * φ g = φ g * φ b) → ∀ a b : G, φ a * φ b = φ b * φ a := by sorry
