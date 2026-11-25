-- Prove2me | Theorems.Thm_GroundTheory_LocalField_sum_conj_eq_card_centralizer
-- name    : GroundTheory.LocalField.sum_conj_eq_card_centralizer
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:33:28.431369+00:00
-- url     : https://prove2.me/theorems/42c3bcfd-6943-48e7-98ab-02f9dbad7146
-- title:
--   Local Field: sum conj eq card centralizer
-- statement:
--   The Local Field construction uses the sum conj eq card centralizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L308-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L308-L325

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

theorem GroundTheory.LocalField.sum_conj_eq_card_centralizer [Fintype G] {g : G} (hc : IsConj x g) :
    (∑ t : G, if t⁻¹ * g * t = x then (1 : ℂ) else 0) = Nat.card (Subgroup.centralizer {x}) := by sorry
