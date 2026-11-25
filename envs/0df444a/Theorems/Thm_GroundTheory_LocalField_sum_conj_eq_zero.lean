-- Prove2me | Theorems.Thm_GroundTheory_LocalField_sum_conj_eq_zero
-- name    : GroundTheory.LocalField.sum_conj_eq_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:33:18.549518+00:00
-- url     : https://prove2.me/theorems/78066fb1-25a9-527a-9b23-0b5ac15197fe
-- title:
--   Local Field: sum conj eq zero
-- statement:
--   The Local Field construction uses the sum conj eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L328-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L328-L332

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
omit [Fintype G] hp

theorem GroundTheory.LocalField.sum_conj_eq_zero [Fintype G] {g : G} (hc : ¬ IsConj x g) :
    (∑ t : G, if t⁻¹ * g * t = x then (1 : ℂ) else 0) = 0 := by sorry
