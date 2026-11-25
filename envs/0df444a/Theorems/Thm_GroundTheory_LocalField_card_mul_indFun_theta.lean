-- Prove2me | Theorems.Thm_GroundTheory_LocalField_card_mul_indFun_theta
-- name    : GroundTheory.LocalField.card_mul_indFun_theta
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:14:51.706525+00:00
-- url     : https://prove2.me/theorems/fcf1a172-01ed-4aa8-9236-714f0b3007b6
-- title:
--   Local Field: card mul ind Fun theta
-- statement:
--   The Local Field construction uses the card mul ind Fun theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L156-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L156-L199

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
omit hp

theorem GroundTheory.LocalField.card_mul_indFun_theta (g : G) :
    (Nat.card (sylowCent p x) : ℂ) * indFun (elemSub p x).subtype (theta p x) g =
      ∑ t : G, if x⁻¹ * (t⁻¹ * g * t) ∈ sylowCent p x then 1 else 0 := by sorry
