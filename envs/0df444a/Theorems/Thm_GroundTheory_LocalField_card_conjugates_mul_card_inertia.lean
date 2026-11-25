-- Prove2me | Theorems.Thm_GroundTheory_LocalField_card_conjugates_mul_card_inertia
-- name    : GroundTheory.LocalField.card_conjugates_mul_card_inertia
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:35:21.343773+00:00
-- url     : https://prove2.me/theorems/a1825bc9-9ef6-4b29-b82f-3b801c72bcbc
-- title:
--   Local Field: card conjugates mul card inertia
-- statement:
--   The Local Field construction uses the card conjugates mul card inertia property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionClifford.lean#L230-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionClifford.lean#L230-L248

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionClifford
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
variable {G : Type*} [Group G] (A : Subgroup G) [hA : A.Normal]
open Classical

theorem GroundTheory.LocalField.card_conjugates_mul_card_inertia [Fintype G] (θ : A → ℂ) :
    (Finset.univ.image fun g : G ↦ θ ∘ conjNormal A g).card * Nat.card (inertia A θ) = Nat.card G := by sorry
