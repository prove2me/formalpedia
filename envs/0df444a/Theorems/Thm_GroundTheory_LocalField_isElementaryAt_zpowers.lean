-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isElementaryAt_zpowers
-- name    : GroundTheory.LocalField.isElementaryAt_zpowers
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:44:42.172527+00:00
-- url     : https://prove2.me/theorems/7364557c-921a-45eb-bb39-dda851d221f7
-- title:
--   Local Field: is Elementary At zpowers
-- statement:
--   The Local Field construction uses the is Elementary At zpowers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionElementary.lean#L39-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionElementary.lean#L39-L61

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionElementary
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
variable {G : Type*} [Group G]
variable [Finite G] {p : ℕ}

theorem GroundTheory.LocalField.isElementaryAt_zpowers (hp : p.Prime) (s : G) : IsElementaryAt p (Subgroup.zpowers s) := by sorry
