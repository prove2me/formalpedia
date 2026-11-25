-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isElementaryAt_elemSub
-- name    : GroundTheory.LocalField.isElementaryAt_elemSub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:35:39.215068+00:00
-- url     : https://prove2.me/theorems/a063ee7d-776a-4deb-b4e1-5ac5a3689c55
-- title:
--   Local Field: is Elementary At elem Sub
-- statement:
--   The Local Field construction uses the is Elementary At elem Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L88-L91

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

theorem GroundTheory.LocalField.isElementaryAt_elemSub (hx : (orderOf x).Coprime p) : IsElementaryAt p (elemSub p x) := by sorry
