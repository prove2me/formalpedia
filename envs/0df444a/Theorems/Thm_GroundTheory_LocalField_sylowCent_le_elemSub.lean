-- Prove2me | Theorems.Thm_GroundTheory_LocalField_sylowCent_le_elemSub
-- name    : GroundTheory.LocalField.sylowCent_le_elemSub
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:33:51.69711+00:00
-- url     : https://prove2.me/theorems/c0d95561-4e34-486f-8838-5b198d24dc6d
-- title:
--   Local Field: sylow Cent le elem Sub
-- statement:
--   The Local Field construction uses the sylow Cent le elem Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L85-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L85-L85

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

theorem GroundTheory.LocalField.sylowCent_le_elemSub : sylowCent p x ≤ elemSub p x := by sorry
