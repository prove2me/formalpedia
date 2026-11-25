-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_extendByZero_coe
-- name    : GroundTheory.Global.Artin.extendByZero_coe
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:45:25.613998+00:00
-- url     : https://prove2.me/theorems/8f5a0759-8fd4-4422-ad00-f2d55eb75af8
-- title:
--   Artin: extend By Zero coe
-- statement:
--   The Artin construction uses the extend By Zero coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/Mackey.lean#L43-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/Mackey.lean#L43-L44

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_TateCohomology_DoubleCosetSum
import Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
open GroundTheory.LocalField
variable {G : Type*} [Group G]

theorem GroundTheory.Global.Artin.extendByZero_coe (H : Subgroup G) (f : H → ℂ) (h : H) : extendByZero H f h = f h := by sorry
