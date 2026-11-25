-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mk_classRep
-- name    : GroundTheory.LocalField.mk_classRep
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:32:40.980018+00:00
-- url     : https://prove2.me/theorems/ea89468d-c0fc-47eb-9cc7-e4b97bd7a40f
-- title:
--   Local Field: mk class Rep
-- statement:
--   The Local Field construction uses the mk class Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L341-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L341-L342

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

theorem GroundTheory.LocalField.mk_classRep (c : ConjClasses G) : ConjClasses.mk (classRep c) = c := by sorry
