-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isPGroup_sylowCent
-- name    : GroundTheory.LocalField.isPGroup_sylowCent
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:20:00.235611+00:00
-- url     : https://prove2.me/theorems/ec220110-a202-583c-8c55-89e6029cbfcf
-- title:
--   Local Field: is PGroup sylow Cent
-- statement:
--   The Local Field construction uses the is PGroup sylow Cent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L58-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L58-L59

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
variable (p x)

theorem GroundTheory.LocalField.isPGroup_sylowCent : IsPGroup p (sylowCent p x) := by sorry
