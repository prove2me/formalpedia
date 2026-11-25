-- Prove2me | Theorems.Thm_GroundTheory_LocalField_card_mul_indFun_theta_of_coprime
-- name    : GroundTheory.LocalField.card_mul_indFun_theta_of_coprime
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:35:51.953688+00:00
-- url     : https://prove2.me/theorems/d71e2707-7e00-44dd-b0d1-5ba656405b07
-- title:
--   Local Field: card mul ind Fun theta of coprime
-- statement:
--   The Local Field construction uses the card mul ind Fun theta of coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L293-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L293-L305

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionPrime
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
open scoped Classical
universe u
variable {G : Type u} [Group G]
variable [Fintype G] (p : ℕ) [hp : Fact p.Prime] (x : G)
variable {p x}

theorem GroundTheory.LocalField.card_mul_indFun_theta_of_coprime (hx : (orderOf x).Coprime p) {g : G}
    (hg : (orderOf g).Coprime p) :
    (Nat.card (sylowCent p x) : ℂ) * indFun (elemSub p x).subtype (theta p x) g =
      ∑ t : G, if t⁻¹ * g * t = x then 1 else 0 := by sorry
