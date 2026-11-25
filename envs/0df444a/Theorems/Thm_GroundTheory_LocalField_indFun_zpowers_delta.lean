-- Prove2me | Theorems.Thm_GroundTheory_LocalField_indFun_zpowers_delta
-- name    : GroundTheory.LocalField.indFun_zpowers_delta
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:36:00.26683+00:00
-- url     : https://prove2.me/theorems/1de67fe0-2bbd-4d76-a8dc-30ba4763e3aa
-- title:
--   Local Field: ind Fun zpowers delta
-- statement:
--   The Local Field construction uses the ind Fun zpowers delta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionLocal.lean#L20-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionLocal.lean#L20-L43

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
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
variable {G : Type u} [Group G] [Fintype G]

theorem GroundTheory.LocalField.indFun_zpowers_delta (s : G) :
    indFun (Subgroup.zpowers s).subtype
      (fun c ↦ if c = ⟨s, Subgroup.mem_zpowers s⟩ then (Nat.card (Subgroup.zpowers s) : ℂ) else 0) =
      classCount s := by sorry
